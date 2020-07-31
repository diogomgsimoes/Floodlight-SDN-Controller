package net.floodlightcontroller.ltmodule;

import java.io.FileNotFoundException;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;

import org.projectfloodlight.openflow.protocol.OFFlowMod;
import org.projectfloodlight.openflow.protocol.OFFlowModCommand;
import org.projectfloodlight.openflow.protocol.OFFlowModFlags;
import org.projectfloodlight.openflow.protocol.OFFlowRemoved;
import org.projectfloodlight.openflow.protocol.OFMessage;
import org.projectfloodlight.openflow.protocol.OFPacketIn;
import org.projectfloodlight.openflow.protocol.OFPacketOut;
import org.projectfloodlight.openflow.protocol.OFType;
import org.projectfloodlight.openflow.protocol.OFVersion;
import org.projectfloodlight.openflow.protocol.action.OFAction;
import org.projectfloodlight.openflow.protocol.action.OFActionOutput;
import org.projectfloodlight.openflow.protocol.action.OFActions;
import org.projectfloodlight.openflow.protocol.instruction.OFInstruction;
import org.projectfloodlight.openflow.protocol.instruction.OFInstructionApplyActions;
import org.projectfloodlight.openflow.protocol.instruction.OFInstructions;
import org.projectfloodlight.openflow.protocol.match.Match;
import org.projectfloodlight.openflow.protocol.match.MatchField;
import org.projectfloodlight.openflow.types.EthType;
import org.projectfloodlight.openflow.types.IPv4Address;
import org.projectfloodlight.openflow.types.IPv4AddressWithMask;
import org.projectfloodlight.openflow.types.IpProtocol;
import org.projectfloodlight.openflow.types.MacAddress;
import org.projectfloodlight.openflow.types.OFBufferId;
import org.projectfloodlight.openflow.types.OFPort;
import org.projectfloodlight.openflow.types.OFVlanVidMatch;
import org.projectfloodlight.openflow.types.TableId;
import org.projectfloodlight.openflow.types.TransportPort;
import org.projectfloodlight.openflow.types.U64;
import org.projectfloodlight.openflow.types.VlanVid;
import org.projectfloodlight.openflow.util.LRULinkedHashMap;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import net.floodlightcontroller.core.FloodlightContext;
import net.floodlightcontroller.core.IControllerCompletionListener;
import net.floodlightcontroller.core.IFloodlightProviderService;
import net.floodlightcontroller.core.IOFMessageListener;
import net.floodlightcontroller.core.IOFSwitch;
import net.floodlightcontroller.core.module.FloodlightModuleContext;
import net.floodlightcontroller.core.module.FloodlightModuleException;
import net.floodlightcontroller.core.module.IFloodlightModule;
import net.floodlightcontroller.core.module.IFloodlightService;
import net.floodlightcontroller.core.types.MacVlanPair;
import net.floodlightcontroller.learningswitch.LearningSwitch;
import net.floodlightcontroller.ltmodule.util.*;
import net.floodlightcontroller.packet.Ethernet;
import net.floodlightcontroller.packet.IPacket;
import net.floodlightcontroller.packet.IPv4;
import net.floodlightcontroller.packet.PacketParsingException;
import net.floodlightcontroller.packet.TCP;
import net.floodlightcontroller.util.OFMessageUtils;

public class LTmodule implements IFloodlightModule, IOFMessageListener {
	protected static Logger log = LoggerFactory.getLogger(LTmodule.class);

	// Module dependencies
	protected IFloodlightProviderService floodlightProviderService;
	
	// flow-mod - cookie if needed
	public static final int LT_MODULE_APP_ID = 1;
	
	// Stores the learned state for each switch
	protected Map<IOFSwitch, Map<MacAddress, OFPort>> macToSwitchPortMap = new ConcurrentHashMap<IOFSwitch, Map<MacAddress, OFPort>>();
	
	public static final int APP_ID_BITS = 12;
	public static final int APP_ID_SHIFT = (64 - APP_ID_BITS);
	public static final long LT_MODULE_COOKIE = (long) (LT_MODULE_APP_ID & ((1 << APP_ID_BITS) - 1)) << APP_ID_SHIFT;
	
	public class Flows {
		IPv4Address sourceIP;
		IPv4Address destinationIP;
		TransportPort sourcePort;
		TransportPort destinationPort;
		MacAddress sourceMac;
		MacAddress destMac;
		ArrayList<TCP> packets;	
		
		public Flows (IPv4Address sourceIP, IPv4Address destinationIP, TransportPort sourcePort, 
				TransportPort destinationPort, MacAddress sourceMac, MacAddress destMac, ArrayList<TCP> packets) {
			this.sourceIP = sourceIP;
			this.destinationIP = destinationIP;
			this.sourceMac = sourceMac;
			this.destMac = destMac;
			this.sourcePort = sourcePort;
			this.destinationPort = destinationPort;
			this.packets = packets;
		}
	}
	
	ArrayList<Flows> flows = new ArrayList<Flows>();
	
	// for managing our map sizes
	protected static final int MAX_MACS_PER_SWITCH  = 1000;
	
	// normally, setup reverse flow as well. Disable only for using cbench for comparison with NOX etc.
	protected static final boolean LEARNING_SWITCH_REVERSE_FLOW = true;

	// more flow-mod defaults
	protected static short FLOWMOD_DEFAULT_IDLE_TIMEOUT = 5; // in seconds
	protected static short FLOWMOD_DEFAULT_HARD_TIMEOUT = 0; // infinite
	protected static short FLOWMOD_PRIORITY = 100;
	

	/**
	 * @param floodlightProvider the floodlightProvider to set
	 */
	public void setFloodlightProvider(IFloodlightProviderService floodlightProviderService) {
		this.floodlightProviderService = floodlightProviderService;
	}

	@Override
	public String getName() {
		return "LTModule";
	}
	
	/**
	 * Adds a host to the MAC->SwitchPort mapping
	 * @param sw The switch to add the mapping to
	 * @param mac The MAC address of the host to add
	 * @param portVal The switchport that the host is on
	 */
	protected void addToPortMap(IOFSwitch sw, MacAddress mac, OFPort portVal) {
		Map<MacAddress, OFPort> swMap = macToSwitchPortMap.get(sw);
		if (swMap == null) {
			swMap = new LRULinkedHashMap<MacAddress, OFPort>(MAX_MACS_PER_SWITCH);
			macToSwitchPortMap.put(sw, swMap);
		}
		swMap.put(mac, portVal);
	}

	/**
	 * Removes a host from the MAC->SwitchPort mapping
	 * @param sw The switch to remove the mapping from
	 * @param mac The MAC address of the host to remove
	 */
	protected void removeFromPortMap(IOFSwitch sw, MacAddress mac) {
		Map<MacAddress, OFPort> swMap = macToSwitchPortMap.get(sw);
		if (swMap != null) {
			swMap.remove(mac);
		}
	}
	
	/**
	 * Get the port that a MAC is associated with
	 * @param sw The switch to get the mapping from
	 * @param mac The MAC address to get
	 * @return The port the host is on
	 */
	public OFPort getFromPortMap(IOFSwitch sw, MacAddress mac) {
		Map<MacAddress, OFPort> swMap = macToSwitchPortMap.get(sw);
		if (swMap != null) {
			return swMap.get(mac);
		}

		// if none found
		return null;
	}

	/**
	 * Clears the MAC -> SwitchPort map for all switches
	 */
	public void clearLearnedTable() {
		macToSwitchPortMap.clear();
	}

	/**
	 * Clears the MAC/VLAN -> SwitchPort map for a single switch
	 * @param sw The switch to clear the mapping for
	 */
	public void clearLearnedTable(IOFSwitch sw) {
		Map<MacAddress, OFPort> swMap = macToSwitchPortMap.get(sw);
		if (swMap != null) {
			swMap.clear();
		}
	}
	
	/**
	 * Processes a OFPacketIn message. If the switch has learned the MAC to port mapping
	 * for the pair it will write a FlowMod for. If the mapping has not been learned the
	 * we will flood the packet.
	 * @param sw
	 * @param pi
	 * @param cntx
	 * @return
	 */
	private Command processPacketInMessage(IOFSwitch sw, OFPacketIn pi, FloodlightContext cntx) {
		
		// Get the Payload of the OpenFlow Packet_In message (an Ethernet packet from which we can get all info) 
		Ethernet eth = IFloodlightProviderService.bcStore.get(cntx, IFloodlightProviderService.CONTEXT_PI_PAYLOAD);		
		/* Read packet header attributes into a Match object */
		MacAddress sourceMac = eth.getSourceMACAddress();
		MacAddress destMac = eth.getDestinationMACAddress();
	
		if (sourceMac == null) {
			sourceMac = MacAddress.NONE;
		}
		if (destMac == null) {
			destMac = MacAddress.NONE;
		}
		
		if ((destMac.getLong() & 0xfffffffffff0L) == 0x0180c2000000L) {
			if (log.isTraceEnabled()) {
				log.trace("ignoring packet addressed to 802.1D/Q reserved addr: switch {} dest MAC {}",
						new Object[]{ sw, destMac.toString() });
			}
			return Command.STOP;
		}
		
		if ((sourceMac.getLong() & 0x010000000000L) == 0) {
			// If source MAC is a unicast address
			this.addToPortMap(sw, sourceMac, pi.getInPort());
			SwitchCommands.sendPacketOutPacketIn(sw, OFPort.FLOOD, pi);	
		
			boolean flow_exists = false;
			IPv4 ipv4 = null;
			TCP tcp = null;
			int flags = 0;
			int i;
			int index = 0;

			// get the port associated with the destination Mac address
			OFPort outPort = getFromPortMap(sw, destMac);
			
			// se for ipv4
			if (eth.getEtherType().equals(EthType.IPv4)) {
				ipv4 = (IPv4) eth.getPayload();
				// se for tcp
				if (ipv4.getProtocol().equals(IpProtocol.TCP)) {
					tcp = (TCP) ipv4.getPayload();
					flags = tcp.getFlags();
					int syn = flags & 2;
					// se nao for syn (ignorar handshake)
					if (syn == 0) {
						int fin = flags & 1;
						IPv4Address sourceIP = ipv4.getSourceAddress();
						IPv4Address destinationIP = ipv4.getDestinationAddress();
						TransportPort sourcePort = tcp.getSourcePort();
						TransportPort destinationPort = tcp.getDestinationPort();
						if (flows.size() > 0) {
							for (i = 0; i < flows.size(); i++) {
								if ((flows.get(i).sourceMac.equals(sourceMac)) && 
										(flows.get(i).destMac.equals(destMac)) && 
										(flows.get(i).destinationIP.equals(destinationIP)) && 
										(flows.get(i).sourceIP.equals(sourceIP)) && 
										(flows.get(i).sourcePort.equals(sourcePort)) && 
										(flows.get(i).destinationPort.equals(destinationPort))) {
									flow_exists = true;
									index = i;
									break;
								}
							}
						}
						// se nao for finish
						if (fin == 0) {
							// se o flow existir, adiciona ao elemento
							if (flow_exists) {
								// se o flow n tiver recebido 3 pacotes adiciona
								if (flows.get(index).packets.size() != 4) {
									flows.get(index).packets.add(tcp);
								}
								// se recebeu, faz a regra
								else {
									// Actions builder
									OFActions actions = sw.getOFFactory().actions(); 
									
									// List of actions
									List<OFAction> al = new ArrayList<OFAction>();
									
									// Add actions
									OFActionOutput output = actions.buildOutput()
											.setPort(outPort)    
											.setMaxLen(0xffFFffFF)
											.build();
									al.add(output);
									
									// Review the IPv4Address with mask and ports
									Match myMatch = sw.getOFFactory().buildMatch()
										    .setExact(MatchField.ETH_TYPE, EthType.IPv4)
										    .setExact(MatchField.IP_PROTO, IpProtocol.TCP)
										    .setExact(MatchField.IPV4_SRC, ipv4.getSourceAddress())
										    .setExact(MatchField.IPV4_DST, ipv4.getDestinationAddress())
										    .setExact(MatchField.TCP_DST, tcp.getDestinationPort())
										    .setExact(MatchField.TCP_SRC, tcp.getSourcePort())
										    .build();
									
									// Set the FlowModCommand
									OFFlowModCommand command;
									command = OFFlowModCommand.ADD;
									
									// Configure BufferID
									OFBufferId bufferId;
									bufferId = OFBufferId.NO_BUFFER;
															
									
									if (pi.getVersion().compareTo(OFVersion.OF_13)==0){
										//instructions builder
										OFInstructions instructions =  sw.getOFFactory().instructions();
										
										//use the instructions builder to build an applyActions instruction with the given action list.
										OFInstructionApplyActions applyActions = instructions.buildApplyActions().setActions(al).build(); 
										
										ArrayList<OFInstruction> instructionList = new ArrayList<OFInstruction>();
										
										//add the applyActions Instruction to the Instruction list
										instructionList.add(applyActions); 
										
										//call to create rule
										writeFlowMod(sw, command, bufferId, myMatch, al, outPort, FLOWMOD_DEFAULT_IDLE_TIMEOUT, FLOWMOD_DEFAULT_HARD_TIMEOUT);
									} else writeFlowMod(sw, command, bufferId, myMatch, al, outPort, FLOWMOD_DEFAULT_IDLE_TIMEOUT, FLOWMOD_DEFAULT_HARD_TIMEOUT);
								}
							}
							// se o flow n existir, criar objeto
							else {
								ArrayList<TCP> packets = new ArrayList<TCP>();
								packets.add(tcp);
								Flows new_flow = new Flows(sourceIP, destinationIP, sourcePort, destinationPort, sourceMac, destMac, packets);
								flows.add(new_flow);
							}
						}
						else {
							flows.remove(index);
							removeFromPortMap(sw, sourceMac);
						}
					}				
				}
			}
		}
		return Command.STOP;
		
	}

	/**
	 * Processes a flow removed message. 
	 * @param sw The switch that sent the flow removed message.
	 * @param flowRemovedMessage The flow removed message.
	 * @return Whether to continue processing this message or stop.
	 */
	private Command processFlowRemovedMessage(IOFSwitch sw, OFFlowRemoved flowRemovedMessage) {
		if (log.isTraceEnabled()) {
			log.trace("{} flow entry removed {}", sw, flowRemovedMessage);
		}
		Match match = flowRemovedMessage.getMatch();
		
		long duration = flowRemovedMessage.getDurationSec();
		U64 byte_count = flowRemovedMessage.getByteCount();
		
		int i;
		
		for (i = 0; i < flows.size(); i++) {
			if ((match.get(MatchField.IPV4_SRC).equals(flows.get(i).sourceIP)) &&
					(match.get(MatchField.IPV4_DST).equals(flows.get(i).destinationIP)) &&
					(match.get(MatchField.TCP_SRC).equals(flows.get(i).sourcePort)) &&
					(match.get(MatchField.TCP_DST).equals(flows.get(i).destinationPort)) &&
					(flows.get(i).packets.get(3).getPayload().serialize().length > 0)) {
				String data = match.get(MatchField.IPV4_SRC).toString() + ',' + match.get(MatchField.IPV4_DST).toString() + ',' + 
						match.get(MatchField.TCP_SRC).toString() + ',' + match.get(MatchField.TCP_DST).toString() + ',' + 
						flows.get(i).packets.get(1).getPayload().serialize().length + ',' +
						flows.get(i).packets.get(2).getPayload().serialize().length + ',' + 
						flows.get(i).packets.get(3).getPayload().serialize().length + ',' + 
						byte_count.getValue() + ',' + duration;	
				
				PrintWriter out = null;
				try {
					out = new PrintWriter("data.txt");
					out.println(data);
				} catch (FileNotFoundException e) {
					e.printStackTrace();
				}
				
				out.close();
				removeFromPortMap(sw, flows.get(i).sourceMac);
				break;
			}
		}
		
		// otimizar (string dos 4 valores como key....)
		// otimizar resultados
		
		// When a flow entry expires, it means the device with the matching source
		// MAC address either stopped sending packets or moved to a different
		// port.  If the device moved, we can't know where it went until it sends
		// another packet, allowing us to re-learn its port.  Meanwhile we remove
		// it from the macToPortMap to revert to flooding packets to this device.
		
		// Also, if packets keep coming from another device (e.g. from ping), the
		// corresponding reverse flow entry will never expire on its own and will
		// send the packets to the wrong port (the matching input port of the
		// expired flow entry), so we must delete the reverse entry explicitly.
		
		return Command.CONTINUE;
	}
	
	private void writeFlowMod(IOFSwitch sw, OFFlowModCommand command, OFBufferId bufferId, Match match, List<OFAction> al, OFPort outPort, short IdleTimeout, short HardTimeout) {
		OFFlowMod.Builder fmb;
		if (command == OFFlowModCommand.DELETE) {
		//build
			fmb = sw.getOFFactory().buildFlowDelete();
		} else {
			fmb = sw.getOFFactory().buildFlowAdd();
		}
		fmb.setMatch(match); // set the match
		fmb.setCookie((U64.of(LT_MODULE_COOKIE))); //cookie to identify that the flow was set by this application
		fmb.setIdleTimeout(IdleTimeout); // set the timeouts
		fmb.setHardTimeout(HardTimeout);
		fmb.setPriority(100); // set priority
		fmb.setBufferId(bufferId);
		fmb.setOutPort((command == OFFlowModCommand.DELETE) ?
		OFPort.ANY : outPort);
		Set<OFFlowModFlags> sfmf = new HashSet<OFFlowModFlags>();
		if (command != OFFlowModCommand.DELETE) {
			sfmf.add(OFFlowModFlags.SEND_FLOW_REM);
		}
		fmb.setFlags(sfmf);
		fmb.setActions(al);
		log.info("{} {} flow mod {}",
		new Object[]{ sw, (command ==
		OFFlowModCommand.DELETE) ? "deleting" : "adding", fmb.build() });
		// build flowMod and write it out
		sw.write(fmb.build());
	}

	// IOFMessageListener

	@Override
	public Command receive(IOFSwitch sw, OFMessage msg, FloodlightContext cntx) {
		switch (msg.getType()) {
		case PACKET_IN:
			return this.processPacketInMessage(sw, (OFPacketIn) msg, cntx);
		case FLOW_REMOVED:
			return this.processFlowRemovedMessage(sw, (OFFlowRemoved) msg);
		case ERROR:
			log.info("received an error {} from switch {}", msg, sw);
			return Command.CONTINUE;
		default:
			log.error("received an unexpected message {} from switch {}", msg, sw);
			return Command.CONTINUE;
		}
	}

	@Override
	public boolean isCallbackOrderingPrereq(OFType type, String name) {
		return false;
	}

	@Override
	public boolean isCallbackOrderingPostreq(OFType type, String name) {
		return (type.equals(OFType.PACKET_IN) && name.equals("forwarding")) ;
	}
	
	// IFloodlightModule

    /**
     * Tell the module system which services we provide.
     */
	@Override
	public Collection<Class<? extends IFloodlightService>> getModuleServices() 
	{ return null; }

	/**
     * Tell the module system which services we implement.
     */
	@Override
	public Map<Class<? extends IFloodlightService>, IFloodlightService> 
			getServiceImpls() 
	{ return null; }

	@Override
	public Collection<Class<? extends IFloodlightService>> getModuleDependencies() {
		Collection<Class<? extends IFloodlightService>> l =
				new ArrayList<Class<? extends IFloodlightService>>();
		l.add(IFloodlightProviderService.class);
		return l;
	}

	@Override
	public void init(FloodlightModuleContext context) throws FloodlightModuleException {
		floodlightProviderService = context.getServiceImpl(IFloodlightProviderService.class);
		log.info("LT module started {}");
	}

	@Override
	public void startUp(FloodlightModuleContext context) {
		// paag: register the IControllerCompletionListener
		floodlightProviderService.addOFMessageListener(OFType.PACKET_IN, this);
		floodlightProviderService.addOFMessageListener(OFType.FLOW_REMOVED, this);
		floodlightProviderService.addOFMessageListener(OFType.ERROR, this);

		// read our config options
		Map<String, String> configOptions = context.getConfigParams(this);
		try {
			String idleTimeout = configOptions.get("idletimeout");
			if (idleTimeout != null) {
				FLOWMOD_DEFAULT_IDLE_TIMEOUT = Short.parseShort(idleTimeout);
			}
		} catch (NumberFormatException e) {
			log.warn("Error parsing flow idle timeout, " +
					"using default of {} seconds", FLOWMOD_DEFAULT_IDLE_TIMEOUT);
		}
		try {
			String hardTimeout = configOptions.get("hardtimeout");
			if (hardTimeout != null) {
				FLOWMOD_DEFAULT_HARD_TIMEOUT = Short.parseShort(hardTimeout);
			}
		} catch (NumberFormatException e) {
			log.warn("Error parsing flow hard timeout, " +
					"using default of {} seconds", FLOWMOD_DEFAULT_HARD_TIMEOUT);
		}
		try {
			String priority = configOptions.get("priority");
			if (priority != null) {
				FLOWMOD_PRIORITY = Short.parseShort(priority);
			}
		} catch (NumberFormatException e) {
			log.warn("Error parsing flow priority, " +
					"using default of {}",
					FLOWMOD_PRIORITY);
		}
		log.debug("FlowMod idle timeout set to {} seconds", FLOWMOD_DEFAULT_IDLE_TIMEOUT);
		log.debug("FlowMod hard timeout set to {} seconds", FLOWMOD_DEFAULT_HARD_TIMEOUT);
		log.debug("FlowMod priority set to {}", FLOWMOD_PRIORITY);
	}

}