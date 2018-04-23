//Copyright (c) 2018 Alex Kallergis

//based on examples from:
// Copyright (C) 2014 Texas Instruments Incorporated - http://www.ti.com/

//LCD code based on:
//Copyright (c) http://karuppuswamy.com/wordpress/2015/03/12/msp430-launchpad-interface-with-16x2-lcd-display/



/*This is the code from my thesis project where an AP is set up with the board,
 * where TCP messages from a client can be sent & printed on the LCD screen.If the message is
 * bigger than 16 chars the message is shifted left until all is displayed.
 * The android app "socket test" was used for the client.
 *

*uC and LCD Connections
*   TP1 - Vcc (+5v)
*   TP3 - Vss (Gnd)
*   GPIO12 - D4
*   GPIO6 - D5
*   GPIO7 - D6
*   GPIO8 - D7
*   GPIO9 - EN
*   GPIO0 - RS
*   Gnd  - RW
*   Gnd  - Vee through 1K Resistor  - this value determines contrast - i.e. direct connection to Gnd means all dots displayed
*   Gnd  - K (LED-)
*   Vcc  - A (LED+) +5V
*   Clock: 1MHz             */


#include <stdio.h>
#include <stdlib.h>
#include <string.h>

// Simplelink includes
#include "simplelink.h"

// driverlib includes 
#include "hw_types.h"
#include "hw_ints.h"
#include "rom.h"
#include "rom_map.h"
#include "interrupt.h"
#include "prcm.h"
#include "utils.h"
#include "gpio.h"
#include "timer.h"      //?
#include "timer_if.h"   //?
#include "hw_memmap.h"  //?
#include "pin.h"

// common interface includes
#include "common.h"
#ifndef NOTERM
#include "uart_if.h"
#endif
#include "pin_mux_config.h"
#include "hw_hib1p2.h"
#include "utils_if.h"

#define OSI_STACK_SIZE          2048

#define IP_ADDR             0xc0a80064 /* 192.168.0.100 */
#define PORT_NUM            5001
#define BUF_SIZE            1400
//#define TCP_PACKET_COUNT    10


extern void(* const g_pfnVectors[])(void); // declare the interrupt vector table as an external table
//
// Values for below macros shall be modified for setting the 'Ping' properties
//
#define PING_INTERVAL       1000    /* In msecs */
#define PING_TIMEOUT        3000    /* In msecs */
#define PING_PKT_SIZE       20      /* In bytes */
#define NO_OF_ATTEMPTS      3
#define PING_FLAG           0

// Application specific status/error codes
typedef enum{
    // Choosing this number to avoid overlap w/ host-driver's error codes 
    LAN_CONNECTION_FAILED = -0x7D0,        
    CLIENT_CONNECTION_FAILED = LAN_CONNECTION_FAILED - 1,
    DEVICE_NOT_IN_STATION_MODE = CLIENT_CONNECTION_FAILED - 1,
    SOCKET_CREATE_ERROR = -0x7D0,
    BIND_ERROR = SOCKET_CREATE_ERROR - 1,
    LISTEN_ERROR = BIND_ERROR -1,
    SOCKET_OPT_ERROR = LISTEN_ERROR -1,
    CONNECT_ERROR = SOCKET_OPT_ERROR -1,
    ACCEPT_ERROR = CONNECT_ERROR - 1,
    SEND_ERROR = ACCEPT_ERROR -1,
    RECV_ERROR = SEND_ERROR -1,
    SOCKET_CLOSE_ERROR = RECV_ERROR -1,
    //DEVICE_NOT_IN_STATION_MODE = SOCKET_CLOSE_ERROR - 1,
    STATUS_CODE_MAX = -0xBB8
}e_AppStatusCodes;


//*****************************************************************************
//                 GLOBAL VARIABLES -- Start
//*****************************************************************************
unsigned char  g_ulStatus = 0;
_u16 TXP=111;
unsigned long  g_ulStaIp = 0;
unsigned long  g_ulPingPacketsRecv = 0;
unsigned long  g_uiGatewayIP = 0;
unsigned long g_ulIpAddr=0;
unsigned long x,s;
unsigned short mis;
unsigned int k,l,bufpointer,size;
float taf=1.0,y,ms;

unsigned long  g_ulDestinationIp = IP_ADDR;
unsigned int   g_uiPortNum = PORT_NUM,i;
//volatile unsigned long  g_ulPacketCount = TCP_PACKET_COUNT;
unsigned char  g_ucConnectionStatus = 0,ucConfigOpt=0;
unsigned char  g_ucSimplelinkstarted = 0;
char g_cBsdBuf[BUF_SIZE],temp[BUF_SIZE],temp2[17];
unsigned long  g_ulGatewayIP = 0; //Network Gateway IP address





#if defined(gcc)
extern void (* const g_pfnVectors[])(void);
#endif
#if defined(ewarm)
extern uVectorEntry __vector_table;
#endif
//*****************************************************************************
//                 GLOBAL VARIABLES -- End
//*****************************************************************************



//****************************************************************************
//                      LOCAL FUNCTION PROTOTYPES
//****************************************************************************

static long ConfigureSimpleLinkToDefaultState();
static void InitializeAppVariables();
void EnterHIBernate(void);
static void BoardInit(void);
void int13(void);
//void clkint(void);


//*****************************************************************************
//
//! Board Initialization & Configuration
//!
//! \param  None
//!
//! \return None
//
//*****************************************************************************
static void BoardInit(void)
{
/* In case of TI-RTOS vector table is initialize by OS itself */
#ifndef USE_TIRTOS
    //
    // Set vector table base
    //
#if defined(ccs)
    MAP_IntVTableBaseSet((unsigned long)&g_pfnVectors[0]);
#endif
#if defined(ewarm)
    MAP_IntVTableBaseSet((unsigned long)&__vector_table);
#endif
#endif
    //
    // Enable Processor
    //
    MAP_IntMasterEnable();
    MAP_IntEnable(FAULT_SYSTICK);

    PRCMCC3200MCUInit();
}




// LCD Registers masks based on pin to which it is connected
#define LCD_EN      0X10
#define LCD_RS      0X20

void updlcdport(int lcdport){
lcdport=lcdport&0x3f;
GPIOPinWrite(GPIOA1_BASE, 0x10,(lcdport&0x1)<<4);     //cc3200 pin 3
GPIOPinWrite(GPIOA0_BASE, 0x40,(lcdport&0x2)<<5);
GPIOPinWrite(GPIOA0_BASE, 0x80,(lcdport&0x4)<<5);
GPIOPinWrite(GPIOA1_BASE, 0x1,(lcdport&0x8)>>3);
GPIOPinWrite(GPIOA1_BASE, 0x2,(lcdport&0x10)>>3);
GPIOPinWrite(GPIOA0_BASE, 0x1,(lcdport&0x20)>>5);
}

void lcd_reset()
{
    //lcd_port_dir = 0xff;    // output mode
    updlcdport(0xff);
    MAP_UtilsDelay(20000*80);
    updlcdport(0x03+LCD_EN);
    updlcdport(0x03);
    MAP_UtilsDelay(10000*80);
    updlcdport(0x03+LCD_EN);
    updlcdport(0x03);
    MAP_UtilsDelay(1000*80);
    updlcdport(0x03+LCD_EN);
    updlcdport(0x03);
    MAP_UtilsDelay(1000*80);
    updlcdport(0x02+LCD_EN);
    updlcdport(0x02);
    MAP_UtilsDelay(1000*80);
}

void lcd_cmd (char cmd)
{
    // Send upper nibble
    updlcdport(((cmd >> 4) & 0x0F)|LCD_EN);
    updlcdport((cmd >> 4) & 0x0F);

    // Send lower nibble
    updlcdport((cmd & 0x0F)|LCD_EN);
    updlcdport(cmd & 0x0F);

    MAP_UtilsDelay(2000*80);
}

void lcd_cmd_fast (char cmd)        //routine for fast commands,smaller delay used
{
    // Send upper nibble
    updlcdport(((cmd >> 4) & 0x0F)|LCD_EN);
    updlcdport((cmd >> 4) & 0x0F);

    // Send lower nibble
    updlcdport((cmd & 0x0F)|LCD_EN);
    updlcdport(cmd & 0x0F);

    MAP_UtilsDelay(100*80);
}


void lcd_init ()
{
    lcd_reset();         // Call LCD reset
    lcd_cmd(0x28);       // 4-bit mode - 2 line - 5x7 font.
    lcd_cmd(0x0C);       // Display no cursor - no blink.
    lcd_cmd(0x06);       // Automatic Increment - No Display shift.
    lcd_cmd(0x80);       // Address DDRAM with 0 offset 80h.
    lcd_cmd(0x01);       // Clear screen
}


void lcd_data (unsigned char dat)
{
    // Send upper nibble
    updlcdport(((dat >> 4) & 0x0F)|LCD_EN|LCD_RS);
    updlcdport(((dat >> 4) & 0x0F)|LCD_RS);

    // Send lower nibble
    updlcdport((dat & 0x0F)|LCD_EN|LCD_RS);
    updlcdport((dat & 0x0F)|LCD_RS);

    MAP_UtilsDelay(100*80); // a small delay may result in missing char display
}

void display_line(char *line)
{
    while (*line)
        lcd_data(*line++);
}




//*****************************************************************************
// SimpleLink Asynchronous Event Handlers -- Start
//*****************************************************************************


//*****************************************************************************
//
//! On Successful completion of Wlan Connect, This function triggers Connection
//! status to be set. 
//!
//! \param  pSlWlanEvent pointer indicating Event type
//!
//! \return None
//!
//*****************************************************************************
void SimpleLinkWlanEventHandler(SlWlanEvent_t *pSlWlanEvent)
{
    switch(pSlWlanEvent->Event)
    {
        case SL_WLAN_CONNECT_EVENT:
        {
            SET_STATUS_BIT(g_ulStatus, STATUS_BIT_CONNECTION);
            UART_PRINT("Wlan connection event \n\r");
            //
            // Information about the connected AP (like name, MAC etc) will be
            // available in 'slWlanConnectAsyncResponse_t'-Applications
            // can use it if required
            //
            //  slWlanConnectAsyncResponse_t *pEventData = NULL;
            // pEventData = &pWlanEvent->EventData.STAandP2PModeWlanConnected;
            //
            //
        }
        break;

        case SL_WLAN_DISCONNECT_EVENT:
        {
            slWlanConnectAsyncResponse_t*  pEventData = NULL;

            CLR_STATUS_BIT(g_ulStatus, STATUS_BIT_CONNECTION);
            CLR_STATUS_BIT(g_ulStatus, STATUS_BIT_IP_AQUIRED);

            pEventData = &pSlWlanEvent->EventData.STAandP2PModeDisconnected;

            // If the user has initiated 'Disconnect' request,
            //'reason_code' is SL_WLAN_DISCONNECT_USER_INITIATED_DISCONNECTION
            if(SL_WLAN_DISCONNECT_USER_INITIATED_DISCONNECTION == pEventData->reason_code)
            {
                UART_PRINT("Device disconnected from the AP on application's "
                            "request \n\r");
            }
            else
            {
                UART_PRINT("Device disconnected from the AP on an ERROR..!! \n\r");
            }

        }
        break;

        case SL_WLAN_STA_CONNECTED_EVENT:
        {
            // when device is in AP mode and any client connects to device cc3xxx
            SET_STATUS_BIT(g_ulStatus, STATUS_BIT_CONNECTION);

            //
            // Information about the connected client (like SSID, MAC etc) will be
            // available in 'slPeerInfoAsyncResponse_t' - Applications
            // can use it if required
            //
            // slPeerInfoAsyncResponse_t *pEventData = NULL;
            // pEventData = &pSlWlanEvent->EventData.APModeStaConnected;
            //

        }
        break;

        case SL_WLAN_STA_DISCONNECTED_EVENT:
        {
            // when client disconnects from device (AP)
            CLR_STATUS_BIT(g_ulStatus, STATUS_BIT_CONNECTION);
            CLR_STATUS_BIT(g_ulStatus, STATUS_BIT_IP_LEASED);

            //
            // Information about the connected client (like SSID, MAC etc) will
            // be available in 'slPeerInfoAsyncResponse_t' - Applications
            // can use it if required
            //
            // slPeerInfoAsyncResponse_t *pEventData = NULL;
            // pEventData = &pSlWlanEvent->EventData.APModestaDisconnected;
            //            
        }
        break;

        default:
        {
            UART_PRINT("[WLAN EVENT] Unexpected event \n\r");
        }
        break;
    }
}

//*****************************************************************************
//
//! \brief This function handles network events such as IP acquisition, IP
//!           leased, IP released etc.
//!
//! \param[in]  pNetAppEvent - Pointer to NetApp Event Info 
//!
//! \return None
//!
//*****************************************************************************
void SimpleLinkNetAppEventHandler(SlNetAppEvent_t *pNetAppEvent)
{
    switch(pNetAppEvent->Event)
    {
    case SL_NETAPP_IPV4_IPACQUIRED_EVENT:
            {
                SlIpV4AcquiredAsync_t *pEventData = NULL;

                SET_STATUS_BIT(g_ulStatus, STATUS_BIT_IP_AQUIRED);

                //Ip Acquired Event Data
                pEventData = &pNetAppEvent->EventData.ipAcquiredV4;

                g_ulIpAddr = pEventData->ip;

                //Gateway IP address
                g_uiGatewayIP = pEventData->gateway;

                UART_PRINT("[NETAPP EVENT] IP Acquired: IP=%d.%d.%d.%d , "
                            "Gateway=%d.%d.%d.%d\n\r",

                            SL_IPV4_BYTE(g_ulIpAddr,3),
                            SL_IPV4_BYTE(g_ulIpAddr,2),
                            SL_IPV4_BYTE(g_ulIpAddr,1),
                            SL_IPV4_BYTE(g_ulIpAddr,0),
                            SL_IPV4_BYTE(g_uiGatewayIP,3),
                            SL_IPV4_BYTE(g_uiGatewayIP,2),
                            SL_IPV4_BYTE(g_uiGatewayIP,1),
                            SL_IPV4_BYTE(g_uiGatewayIP,0));
            }
            break;
        case SL_NETAPP_IPV6_IPACQUIRED_EVENT:
        {
            SET_STATUS_BIT(g_ulStatus, STATUS_BIT_IP_AQUIRED);
            UART_PRINT("IPV6 ACQUIRED\n\r");
        }
        break;
        
        case SL_NETAPP_IP_LEASED_EVENT:
        {
            SET_STATUS_BIT(g_ulStatus, STATUS_BIT_IP_LEASED);
        
            g_ulStaIp = (pNetAppEvent)->EventData.ipLeased.ip_address;
            
            UART_PRINT("[NETAPP EVENT] IP Leased to Client: IP=%d.%d.%d.%d , \n\r",
                        SL_IPV4_BYTE(g_ulStaIp,3), SL_IPV4_BYTE(g_ulStaIp,2),
                        SL_IPV4_BYTE(g_ulStaIp,1), SL_IPV4_BYTE(g_ulStaIp,0));
        }
        break;
        
        case SL_NETAPP_IP_RELEASED_EVENT:
        {
            CLR_STATUS_BIT(g_ulStatus, STATUS_BIT_IP_LEASED);

            UART_PRINT("[NETAPP EVENT] IP Released for Client: IP=%d.%d.%d.%d , \n\r",
                        SL_IPV4_BYTE(g_ulStaIp,3), SL_IPV4_BYTE(g_ulStaIp,2),
                        SL_IPV4_BYTE(g_ulStaIp,1), SL_IPV4_BYTE(g_ulStaIp,0));

        }
        break;

        default:
        {
            UART_PRINT("[NETAPP EVENT] Unexpected event [0x%x] \n\r",
                       pNetAppEvent->Event);
        }
        break;
    }
}


//*****************************************************************************
//
//! \brief This function handles HTTP server events
//!
//! \param[in]  pServerEvent - Contains the relevant event information
//! \param[in]    pServerResponse - Should be filled by the user with the
//!                                      relevant response information
//!
//! \return None
//!
//****************************************************************************
void SimpleLinkHttpServerCallback(SlHttpServerEvent_t *pHttpEvent,
                                  SlHttpServerResponse_t *pHttpResponse)
{
    // Unused in this application
}

//*****************************************************************************
//
//! \brief This function handles General Events
//!
//! \param[in]     pDevEvent - Pointer to General Event Info 
//!
//! \return None
//!
//*****************************************************************************
void SimpleLinkGeneralEventHandler(SlDeviceEvent_t *pDevEvent)
{
    //
    // Most of the general errors are not FATAL are are to be handled
    // appropriately by the application
    //
    UART_PRINT("[GENERAL EVENT] - ID=[%d] Sender=[%d]\n\n",
               pDevEvent->EventData.deviceEvent.status, 
               pDevEvent->EventData.deviceEvent.sender);
}


//*****************************************************************************
//
//! This function handles socket events indication
//!
//! \param[in]      pSock - Pointer to Socket Event Info
//!
//! \return None
//!
//*****************************************************************************
void SimpleLinkSockEventHandler(SlSockEvent_t *pSock)
{
    //
    // This application doesn't work w/ socket - Events are not expected
    //
    switch( pSock->Event )
    {
        case SL_SOCKET_TX_FAILED_EVENT:
            switch( pSock->socketAsyncEvent.SockTxFailData.status)
            {
                case SL_ECLOSE: 
                    UART_PRINT("[SOCK ERROR] - close socket (%d) operation "
                                "failed to transmit all queued packets\n\n", 
                                    pSock->socketAsyncEvent.SockTxFailData.sd);
                    break;
                default: 
                    UART_PRINT("[SOCK ERROR] - TX FAILED  :  socket %d , reason "
                                "(%d) \n\n",
                                pSock->socketAsyncEvent.SockTxFailData.sd, pSock->socketAsyncEvent.SockTxFailData.status);
                  break;
            }
            break;

        default:
        	UART_PRINT("[SOCK EVENT] - Unexpected Event [%x0x]\n\n",pSock->Event);
          break;
    }

}

//*****************************************************************************
//
//! \brief This function handles ping report events
//!
//! \param[in]     pPingReport - Ping report statistics
//!
//! \return None
//
//****************************************************************************
void SimpleLinkPingReport(SlPingReport_t *pPingReport)
{
    SET_STATUS_BIT(g_ulStatus, STATUS_BIT_PING_DONE);
    g_ulPingPacketsRecv = pPingReport->PacketsReceived;
}

//*****************************************************************************
// SimpleLink Asynchronous Event Handlers -- End
//*****************************************************************************


//*****************************************************************************
//
//! This function initializes the application variables
//!
//! \param[in]    None
//!
//! \return None
//!
//*****************************************************************************
static void InitializeAppVariables()
{    g_ulPingPacketsRecv = 0;

    g_ulStatus = 0;
    g_ulGatewayIP = 0;
    g_ulDestinationIp = IP_ADDR;
    g_uiPortNum = PORT_NUM;

}


//*****************************************************************************
//! \brief This function puts the device in its default state. It:
//!           - Set the mode to STATION
//!           - Configures connection policy to Auto and AutoSmartConfig
//!           - Deletes all the stored profiles
//!           - Enables DHCP
//!           - Disables Scan policy
//!           - Sets Tx power to maximum
//!           - Sets power policy to normal
//!           - Unregister mDNS services
//!           - Remove all filters
//!
//! \param   none
//! \return  On success, zero is returned. On error, negative is returned
//*****************************************************************************
static long ConfigureSimpleLinkToDefaultState()
{
    SlVersionFull   ver = {0};
    _WlanRxFilterOperationCommandBuff_t  RxFilterIdMask = {0};

    unsigned char ucVal = 1;
    unsigned char ucConfigOpt = 0;
    unsigned char ucConfigLen = 0;
    unsigned char ucPower = 0;

    long lRetVal = -1;
    long lMode = -1;

    lMode = sl_Start(0, 0, 0);
    ASSERT_ON_ERROR(lMode);

    // If the device is not in station-mode, try configuring it in station-mode 
    if (ROLE_STA != lMode)
    {
        if (ROLE_AP == lMode)
        {
            // If the device is in AP mode, we need to wait for this event 
            // before doing anything 
            while(!IS_IP_ACQUIRED(g_ulStatus))
            {
#ifndef SL_PLATFORM_MULTI_THREADED
              _SlNonOsMainLoopTask(); 
#endif
            }
        }

        // Switch to STA role and restart 
        lRetVal = sl_WlanSetMode(ROLE_STA);
        ASSERT_ON_ERROR(lRetVal);

        lRetVal = sl_Stop(0xFF);
        ASSERT_ON_ERROR(lRetVal);

        lRetVal = sl_Start(0, 0, 0);
        ASSERT_ON_ERROR(lRetVal);

        // Check if the device is in station again 
        if (ROLE_STA != lRetVal)
        {
            // We don't want to proceed if the device is not coming up in STA-mode 
            return DEVICE_NOT_IN_STATION_MODE;
        }
    }
    
    // Get the device's version-information
    ucConfigOpt = SL_DEVICE_GENERAL_VERSION;
    ucConfigLen = sizeof(ver);
    lRetVal = sl_DevGet(SL_DEVICE_GENERAL_CONFIGURATION, &ucConfigOpt, 
                                &ucConfigLen, (unsigned char *)(&ver));
    ASSERT_ON_ERROR(lRetVal);
    
    UART_PRINT("Host Driver Version: %s\n\r",SL_DRIVER_VERSION);
    UART_PRINT("Build Version %d.%d.%d.%d.31.%d.%d.%d.%d.%d.%d.%d.%d\n\r",
    ver.NwpVersion[0],ver.NwpVersion[1],ver.NwpVersion[2],ver.NwpVersion[3],
    ver.ChipFwAndPhyVersion.FwVersion[0],ver.ChipFwAndPhyVersion.FwVersion[1],
    ver.ChipFwAndPhyVersion.FwVersion[2],ver.ChipFwAndPhyVersion.FwVersion[3],
    ver.ChipFwAndPhyVersion.PhyVersion[0],ver.ChipFwAndPhyVersion.PhyVersion[1],
    ver.ChipFwAndPhyVersion.PhyVersion[2],ver.ChipFwAndPhyVersion.PhyVersion[3]);

    // Set connection policy to Auto + SmartConfig 
    //      (Device's default connection policy)
    lRetVal = sl_WlanPolicySet(SL_POLICY_CONNECTION, 
                                SL_CONNECTION_POLICY(1, 0, 0, 0, 1), NULL, 0);
    ASSERT_ON_ERROR(lRetVal);

    // Remove all profiles
    lRetVal = sl_WlanProfileDel(0xFF);
    ASSERT_ON_ERROR(lRetVal);

    

    //
    // Device in station-mode. Disconnect previous connection if any
    // The function returns 0 if 'Disconnected done', negative number if already
    // disconnected Wait for 'disconnection' event if 0 is returned, Ignore 
    // other return-codes
    //
    lRetVal = sl_WlanDisconnect();
    if(0 == lRetVal)
    {
        // Wait
        while(IS_CONNECTED(g_ulStatus))
        {
#ifndef SL_PLATFORM_MULTI_THREADED
              _SlNonOsMainLoopTask(); 
#endif
        }
    }

    // Enable DHCP client
    lRetVal = sl_NetCfgSet(SL_IPV4_STA_P2P_CL_DHCP_ENABLE,1,1,&ucVal);
    ASSERT_ON_ERROR(lRetVal);

    // Disable scan
    ucConfigOpt = SL_SCAN_POLICY(0);
    lRetVal = sl_WlanPolicySet(SL_POLICY_SCAN , ucConfigOpt, NULL, 0);
    ASSERT_ON_ERROR(lRetVal);

    // Set Tx power level for station mode
    // Number between 0-15, as dB offset from max power - 0 will set max power
    ucPower = 0;
    lRetVal = sl_WlanSet(SL_WLAN_CFG_GENERAL_PARAM_ID, 
            WLAN_GENERAL_PARAM_OPT_STA_TX_POWER, 1, (unsigned char *)&ucPower);
    ASSERT_ON_ERROR(lRetVal);

    // Set PM policy to normal
    lRetVal = sl_WlanPolicySet(SL_POLICY_PM , SL_NORMAL_POLICY, NULL, 0);
    ASSERT_ON_ERROR(lRetVal);

    // Unregister mDNS services
    lRetVal = sl_NetAppMDNSUnRegisterService(0, 0);
    ASSERT_ON_ERROR(lRetVal);

    // Remove  all 64 filters (8*8)
    memset(RxFilterIdMask.FilterIdMask, 0xFF, 8);
    lRetVal = sl_WlanRxFilterSet(SL_REMOVE_RX_FILTER, (_u8 *)&RxFilterIdMask,
                       sizeof(_WlanRxFilterOperationCommandBuff_t));
    ASSERT_ON_ERROR(lRetVal);

    lRetVal = sl_Stop(SL_STOP_TIMEOUT);
    ASSERT_ON_ERROR(lRetVal);

    InitializeAppVariables();
    
    return lRetVal; // Success
}



//****************************************************************************
//
//! Confgiures the mode in which the device will work
//!
//! \param iMode is the current mode of the device
//!
//! This function
//!    1. prompt user for desired configuration and accordingly configure the
//!          networking mode(STA or AP).
//!       2. also give the user the option to configure the ssid name in case of
//!       AP mode.
//!
//! \return sl_start return value(int).
//
//****************************************************************************
static int ConfigureMode(int iMode)
{
    char    pcSsidName[33]="cctestAP";
    long   lRetVal = -1;

    lRetVal = sl_WlanSetMode(ROLE_AP);
    ASSERT_ON_ERROR(lRetVal);

    lRetVal = sl_WlanSet(SL_WLAN_CFG_AP_ID, WLAN_AP_OPT_SSID, strlen(pcSsidName),
                            (unsigned char*)pcSsidName);
    ASSERT_ON_ERROR(lRetVal);

    //UART_PRINT("Device is configured in AP mode\n\r");

    /* Restart Network processor */
    lRetVal = sl_Stop(SL_STOP_TIMEOUT);

    // reset status bits
    CLR_STATUS_BIT_ALL(g_ulStatus);

    return sl_Start(NULL,NULL,NULL);
}


//****************************************************************************
//
//!    \brief start simplelink, wait for the sta to connect to the device and 
//!        run the ping test for that sta
//!
//!    \param  pvparameters is the pointer to the list of parameters that can be
//!         passed to the task while creating it
//!
//!    \return None
//
//****************************************************************************
void WlanAPMode( void)
{   

    unsigned char ucDHCP;
    long lRetVal = -1;

    InitializeAppVariables();

    //
    // Following function configure the device to default state by cleaning
    // the persistent settings stored in NVMEM (viz. connection profiles &
    // policies, power policy etc)
    //
    // Applications may choose to skip this step if the developer is sure
    // that the device is in its default state at start of applicaton
    //
    // Note that all profiles and persistent settings that were done on the
    // device will be lost
    //

    if(MAP_PRCMSysResetCauseGet() != PRCM_HIB_EXIT)
            {

    lRetVal = ConfigureSimpleLinkToDefaultState();


    if(lRetVal < 0)
    {
        if (DEVICE_NOT_IN_STATION_MODE == lRetVal)
            UART_PRINT("Failed to configure the device in its default state \n\r");

        LOOP_FOREVER();
    }

    UART_PRINT("Device is configured in default state \n\r");
            }

    //
    // Asumption is that the device is configured in station mode already
    // and it is in its default state
    //
    lRetVal = sl_Start(NULL,NULL,NULL); //here takes ~100ms...


    if (lRetVal < 0)
    {
        UART_PRINT("Failed to start the device \n\r");
        LOOP_FOREVER();
    }

    //UART_PRINT("Device started as STATION \n\r");

    //
    // Configure the networking mode and ssid name(for AP mode)
    //
    if(lRetVal != ROLE_AP)
    {
        if(ConfigureMode(lRetVal) != ROLE_AP)
        {
            UART_PRINT("Unable to set AP mode, exiting Application...\n\r");
            sl_Stop(SL_STOP_TIMEOUT);
            LOOP_FOREVER();
        }
    }


    while(!IS_IP_ACQUIRED(g_ulStatus))
    {
#ifndef SL_PLATFORM_MULTI_THREADED
      _SlNonOsMainLoopTask();
#endif
    }



    unsigned char len = sizeof(SlNetCfgIpV4Args_t);
    SlNetCfgIpV4Args_t ipV4 = {0};

    // get network configuration
    lRetVal = sl_NetCfgGet(SL_IPV4_AP_P2P_GO_GET_INFO,&ucDHCP,&len,
                            (unsigned char *)&ipV4);
    if (lRetVal < 0)
    {
        UART_PRINT("Failed to get network configuration \n\r");
        LOOP_FOREVER();
    }
    l=WLAN_GENERAL_PARAM_OPT_AP_TX_POWER;
    k=sizeof(TXP);
    sl_WlanGet(SL_WLAN_CFG_GENERAL_PARAM_ID,
                &l, &k, (_u8 *)&TXP);
    UART_PRINT("%d,%s\n\r",TXP,TXP);




    UART_PRINT("\n\rDevice IP: %d.%d.%d.%d\n\r\n\r",
                      SL_IPV4_BYTE(g_ulIpAddr,3),
                      SL_IPV4_BYTE(g_ulIpAddr,2),
                      SL_IPV4_BYTE(g_ulIpAddr,1),
                      SL_IPV4_BYTE(g_ulIpAddr,0));

    UART_PRINT("Default settings: SSID Name: %s, PORT = %d, "
                    "Destination IP: %d.%d.%d.%d\n\r",
                    SSID_NAME, g_uiPortNum,
                    SL_IPV4_BYTE(g_ulDestinationIp,3),
                    SL_IPV4_BYTE(g_ulDestinationIp,2),
                    SL_IPV4_BYTE(g_ulDestinationIp,1),
                    SL_IPV4_BYTE(g_ulDestinationIp,0));




        SlSockAddrIn_t  sAddr;
        SlSockAddrIn_t  sLocalAddr;
        int             iCounter;
        int             iAddrSize;
        int             iSockID;
        int             iStatus;
        int             iNewSockID;
        long            lLoopCount = 0;
        long            lNonBlocking = 1;
        int             iTestBufLen;

        // filling the buffer,NOT NOW
/*        for (iCounter=0 ; iCounter<BUF_SIZE ; iCounter++)
        {
            k=strlen(g_cBsdBuf);
            k=sizeof(g_cBsdBuf);
            g_cBsdBuf[iCounter] = (char)(iCounter % 10);
            strcpy(&g_cBsdBuf[1],"ayyy");
            k=strlen(g_cBsdBuf);
            strcpy(g_cBsdBuf,"ayyy");
        }
*/
        iTestBufLen  = BUF_SIZE;

        //filling the TCP server socket address
        sLocalAddr.sin_family = SL_AF_INET;
        sLocalAddr.sin_port = sl_Htons((unsigned short)g_uiPortNum);
        sLocalAddr.sin_addr.s_addr = 0;

        // creating a TCP socket
        iSockID = sl_Socket(SL_AF_INET,SL_SOCK_STREAM, 0);
        if( iSockID < 0 )
        {
            // error
            ASSERT_ON_ERROR(SOCKET_CREATE_ERROR);
        }

        iAddrSize = sizeof(SlSockAddrIn_t);

        // binding the TCP socket to the TCP server address
        iStatus = sl_Bind(iSockID, (SlSockAddr_t *)&sLocalAddr, iAddrSize);
        if( iStatus < 0 )
        {
            // error
            sl_Close(iSockID);
            ASSERT_ON_ERROR(BIND_ERROR);
        }

        // putting the socket for listening to the incoming TCP connection
        iStatus = sl_Listen(iSockID, 0);
        if( iStatus < 0 )
        {
            sl_Close(iSockID);
            ASSERT_ON_ERROR(LISTEN_ERROR);
        }

        // setting socket option to make the socket as non blocking
        iStatus = sl_SetSockOpt(iSockID, SL_SOL_SOCKET, SL_SO_NONBLOCKING,
                                &lNonBlocking, sizeof(lNonBlocking));
        if( iStatus < 0 )
        {
            sl_Close(iSockID);
            ASSERT_ON_ERROR(SOCKET_OPT_ERROR);
        }
        iNewSockID = SL_EAGAIN;

        // waiting for an incoming TCP connection
        while( iNewSockID < 0 )
        {   lcd_cmd(0x80);          //cursor @0,0
            display_line("waiting for");
            lcd_cmd(0xc0);          //cursor @0,0
            display_line("connection...");
            // accepts a connection form a TCP client, if there is any
            // otherwise returns SL_EAGAIN
            iNewSockID = sl_Accept(iSockID, ( struct SlSockAddr_t *)&sAddr,
                                    (SlSocklen_t*)&iAddrSize);
            if( iNewSockID == SL_EAGAIN )
            {
               MAP_UtilsDelay(10000);
            }
            else if( iNewSockID < 0 )
            {
                // error
                sl_Close(iNewSockID);
                sl_Close(iSockID);
                ASSERT_ON_ERROR(ACCEPT_ERROR);
            }
        }

        // waits for packets from the connected TCP client until disconnected
        while (1)
        {   lcd_cmd(0x80);          //cursor @0,0
            display_line("SEND TCP MESSAGE");
            lcd_cmd(0xc0);          //cursor @0,0
            display_line("                ");
            iStatus = sl_Recv(iNewSockID, g_cBsdBuf, iTestBufLen, 0);
            if( iStatus <= 0 )
            {
              // error
              sl_Close(iNewSockID);
              sl_Close(iSockID);
              UART_PRINT("MSG NOT RECEIVED\n\r");
              //ASSERT_ON_ERROR(RECV_ERROR);
              break;
            }
            else if (strlen(g_cBsdBuf)<900){
                //screen...
                //size=strlen(a);
                UART_PRINT("MSG RECEIVED\n\r");
                //NO sprintf(a,"U wrote:%s",a); //NO. INSTEAD:
                sprintf(temp,"TCP message:%s",g_cBsdBuf);
                strcpy(g_cBsdBuf, temp);
                size=strlen(g_cBsdBuf);
                lcd_cmd(0x80);          //cursor @0,0
                memcpy(temp2,g_cBsdBuf,16);
                display_line("                ");
                lcd_cmd(0x80);          //cursor @0,0
                display_line(temp2);
                MAP_UtilsDelay(60000000);
                if (size>16){
                    for (i=0;i<(size-15);i++){
                        lcd_cmd(0x80);          //cursor @0,0
                        //have to print a string of equal /less than 16 bytes,otherwise lcd will put chars in the other row too
                        memcpy(temp2,&g_cBsdBuf[i],16);
                        //the copy can also be done:
                        //strncpy(temp2,&a[i],16);
                        //n=temp2;
                        //n=&temp2[0];
                        //n=&temp2[-1];
                        //memcpy((temp2+16),NULL,1); //(not really needed,last character is initialized null anyway.) or,
                        //temp2[16]='\0';
                        display_line(temp2);
                        MAP_UtilsDelay(10000000);
                            }
                        }
                MAP_UtilsDelay(30000000);
            }
            else{
                lcd_cmd(0x80);          //cursor @0,0
                display_line("MSG TOO BIG");
                MAP_UtilsDelay(30000000);
            }
            //i=0;
            //NULL=='\0'
            for(i=0;g_cBsdBuf[i]!=NULL;i++){
                g_cBsdBuf[i]=NULL;
            }
            lLoopCount++;
        }

        // close the connected socket after receiving from connected TCP client
        iStatus = sl_Close(iNewSockID);
        //ASSERT_ON_ERROR(iStatus);
        // close the listening socket
        iStatus = sl_Close(iSockID);
        //ASSERT_ON_ERROR(iStatus);


    // Switch off Network processor
    lRetVal = sl_Stop(0);
    EnterHIBernate();

}



void int13(void){
    GPIOIntClear(GPIOA1_BASE,GPIO_PIN_5);
    EnterHIBernate();
}


/*void clkint(void)
{
    IntPendClear(INT_PRCM);
    UtilsDelay(100);
}*/

void EnterHIBernate(void)
{
    GPIOPinWrite(GPIOA1_BASE, GPIO_PIN_3,0);  //GP11
    PRCMHibernateWakeUpGPIOSelect(PRCM_HIB_GPIO13,
                                  PRCM_HIB_RISE_EDGE);
    MAP_PRCMHibernateWakeupSourceEnable(PRCM_HIB_GPIO13);

    UART_PRINT("entering HIB..\n\r");
    MAP_UtilsDelay(80000);

    //
    // powering down SPI Flash to save power
    //
    Utils_SpiFlashDeepPowerDown();
    //
    // Enter HIBernate mode
    //
    MAP_PRCMHibernateEnter();
}

//*****************************************************************************
//                            MAIN FUNCTION
//*****************************************************************************
void main()
{


    //
    // Board Initialization
    //
    BoardInit();
    
    //
    // Configure the pinmux settings for the peripherals exercised
    //
    PinMuxConfig();
    
#ifndef NOTERM
    //
    // Configuring UART
    //
    InitTerm();
#endif

    MAP_UtilsDelay(10000000);   //debounce

    //Configure gpio13 for interupt&wakeup:
    GPIOIntTypeSet(GPIOA1_BASE,GPIO_PIN_5,GPIO_RISING_EDGE);
    GPIOIntRegister(GPIOA1_BASE,int13);
    GPIOIntClear(GPIOA1_BASE,GPIO_PIN_5);
    GPIOIntEnable(GPIOA1_BASE,GPIO_PIN_5);

    //initialize lcd:
    lcd_init();
    MAP_UtilsDelay(10000000);

    UART_PRINT("\n\rprogram start.. \n\r");

/*
    PRCMRTCInUseSet();
    //IntRegister(INT_PRCM,clkint);
    //IntEnable(INT_PRCM);
    PRCMRTCSet(0,0);
    //PRCMRTCMatchSet(1,200);
    PRCMRTCGet(&s,&mis);
    //UART_PRINT("s=%d,ms=%d \n\r",s,mis);
    MAP_UtilsDelay(80000000);
    PRCMRTCGet(&s,&mis);
    //UART_PRINT("s=%d,ms=%d \n\r",s,mis);
*/

    //x=PinDirModeGet(PIN_02);    //doesnt work for some reason...
    //x=GPIODirModeGet(GPIOA1_BASE,0x8);  //this instruction actually takes ucPin>>1...
    GPIOPinWrite(GPIOA1_BASE, GPIO_PIN_1,0);  //GP9
    GPIOPinWrite(GPIOA1_BASE, GPIO_PIN_2,0);  //GP10
    GPIOPinWrite(GPIOA1_BASE, GPIO_PIN_3,1<<3);  //GP11


    //
    // Start the WlanAPMode task
    //
    WlanAPMode();


}
