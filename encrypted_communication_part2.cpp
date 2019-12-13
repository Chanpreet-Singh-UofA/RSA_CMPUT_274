    
//-----------------------------------------------------------------------------------------------------
//
// Name: Chanpreet Singh (1576137)
//       Kaiwen Tang (1575518)
// CMPUT 274 - Tangible Compting - Fall 2019
// Major Assignment 2 part 2
//
//------------------------------------------------------------------------------------------------------


#include <Arduino.h>

int Pin = 13;


//------------------------------------------------------------------------------------------

void setup() {
	init();
	Serial.begin(9600);
    Serial3.begin(9600);
    pinMode(Pin, INPUT);
}

//------------------------------------------------------------------------------------------

// Citation: Provided in the assigment.
void uint32_to_serial3(uint32_t num) {
	Serial3.write((char) (num >> 0));
	Serial3.write((char) (num >> 8));
	Serial3.write((char) (num >> 16));
	Serial3.write((char) (num >> 24));
}

uint32_t uint32_from_serial3() {
	uint32_t num = 0;
	num = num | ((uint32_t) Serial3.read()) << 0;
	num = num | ((uint32_t) Serial3.read()) << 8;
	num = num | ((uint32_t) Serial3.read()) << 16;
	num = num | ((uint32_t) Serial3.read()) << 24;
	return num;
}

//--------------------------------------------------------------------------------------------

uint32_t mod_multiply(uint32_t a, uint32_t b, uint32_t mod) {
    //Perform (a*b) mod m, carefully for both a and b 31-bit numbers in a 32-bit tpye.
    uint32_t pow = b % mod;
    a = a % mod;
    uint32_t ans = 0;
    while (a > 0) {
    	if (a & 1 == 1) {
            //Executed whenever LSB is 1 only
            ans = (ans + pow) % mod;
    	}

    	pow = (pow * 2) % mod;
    	a >>= 1;
    }
    return ans;
}

//--------------------------------------------------------------------------------------------

uint32_t encrypt(uint32_t original_info,uint32_t e,uint32_t m) {

    //We encrypt using RSA encryption scheme, encrypted_info = (original_info)^e(public key) % m (modulus). Modulus should be same for encryption and decryption.

	uint32_t encrypted_info = 1;
	uint32_t pow_x = original_info;
	uint32_t publickey = e;
	uint32_t modulus = m;

	while (publickey > 0) {
	    if (publickey & 1 == 1) {
            //mod_multipy is used to calculate (a*b) % m
            encrypted_info = mod_multiply(encrypted_info, pow_x, modulus);
	    } 
	    pow_x = mod_multiply(pow_x, pow_x, modulus);
	    publickey >>= 1;
    }

    return encrypted_info;
}

//--------------------------------------------------------------------------------------------

uint32_t decrypt(uint32_t encrypted_info,uint32_t d,uint32_t n) {

    //We decrypt using RSA decryption scheme, decrypted_info = (encrypted_info)^d(private key) % m (modulus). Modulus should be same for encryption and decryption.
	uint32_t decrypted_info = 1;
	uint32_t pow_x = encrypted_info;
	uint32_t privatekey = d;
	uint32_t modulus = n;

    while (privatekey > 0) {
	    if (privatekey & 1 == 1) {
            decrypted_info = mod_multiply(decrypted_info, pow_x, modulus);
	    } 
	    pow_x = mod_multiply(pow_x, pow_x, modulus);
	    privatekey >>= 1;
    }

    return decrypted_info;
}

//--------------------------------------------------------------------------------------

// This function is used to generate a random n-bit number using the fuctuation at pin 1. 
uint32_t n_bit_num(uint32_t n_bit){

    uint32_t bit=0,result=0;

    for(uint32_t i=0;i<(n_bit);i++){
        bit=analogRead(1);
        result=(result<<1);
        result= (result|(bit&1));
        delay(5);

    }
    //after geting n-bit number we add it too 2^n to get it in [2^n,2^(n+1)] range
    result=result+((uint32_t)1<<(n_bit));
    return (result);
}

//-----------------------------------------------------------------------------------------------------

// This function is used to check if a number is a  prime number or not.
// Returns : 1 if number is prime number or 0 if not. 
uint32_t primetest(uint32_t p){

    for(uint32_t i=2;i<sqrt(p);i++){
        if((p%i)==0){
            return 0;
        }
    }
    return 1;
}

//---------------------------------------------------------------------------------------------------

//Citation : Program provided by professor in lecture.

uint32_t gcd(uint32_t a, uint32_t b) {
    //fast algoritham to calculate greatest common divisor for a and b.
    while (b > 0) {
        a %= b;
        uint32_t tmp = a;
        a = b;
        b = tmp;
    }
    return a; 
}

//--------------------------------------------------------------------------------------------------

uint32_t calculate_e(uint32_t totient){
    uint32_t e=n_bit_num(15);
    while(gcd(e,totient)!=1){
        e++;
    }
    return e;
}

//--------------------------------------------------------------------------------------------------

// This funvtion is used to adjust d so that its in range 0 <= d < phi_n. 
int32_t reduced_mod(int32_t x, int32_t m){
    if (x>=0){
        return (x%m);
    }
    else{
        int32_t z=((-x/m)+1)%m;
        return ((x+(z*m))%m);
    }
}
//--------------------------------------------------------------------------------------------------

uint32_t calculate_d(uint32_t e, uint32_t phi_n){

    uint32_t r[100];
    uint32_t s[100];
    uint32_t t[100];
    if (gcd(e, phi_n) != 1)  
        //So we return 1 indication to generate another e and try computing d.
        return 1; 
    else
        //We find an integer d such that (e*d) == 1 (mod phi_n) using the Extended Euclidean Algorithm
    
        r[0] = e, r[1] = phi_n;
        s[0] = 1, s[1] = 0;
        t[0]=0, t[1]=1;

        uint32_t i = 1;
        while (r[i] > 0){
            uint32_t q = r[i-1]/r[i];          
            r[i+1] = r[i-1] - q*r[i];  // same as r[i-1] mod r[i]
            s[i+1] = s[i-1] - q*s[i];
            t[i+1] = t[i-1] - q*t[i];
            i = i+1;
        }

        int32_t d = s[i-1];

        if (d < 0 or d >= phi_n){
            //using the worksheet ideas to adjust d so 0 <= d < phi_n
            d=reduced_mod(d,phi_n);
        }

        return d;

}

//--------------------------------------------------------------------------------------------

uint32_t find_keys_mod(uint32_t& d, uint32_t& n, uint32_t& e){

    //Computing a 14-bit prime number
    uint32_t p=n_bit_num(14);//gives a 14 bit number
    while(primetest(p)!=1){
        p=n_bit_num(14);
    }

    uint32_t q=n_bit_num(15);
    while(primetest(q)!=1){
        q=n_bit_num(15);
    }

    //Arduino's modulus
    n=p*q; 

    uint32_t totient=(p-1)*(q-1);

    //Arduinos public key
    e=calculate_e(totient); 

    //Arduinos private key
    d=calculate_d(e,totient); 

    //if d==1 then it mean we need another e value to compute d. Suggested lectures notes on euclid extended algorithm to do.
    while(d==1){
        e=calculate_e(totient);
        d=calculate_d(e,totient);
    }

    //This is a test to confirm if keys are computer correctly and display message to make the program more user friendly and keep user informed about the background program running.
    //This is done totally desirably and was not asked by assignment to do so.
    uint32_t check=mod_multiply(e,d,totient); 
    if(check==1){
        Serial.println("Keys are computed correctly");
    }
}

//----------------------------------------------------------------------------------------------

// initiate all states for server and client to use during handshake
enum StateNames {
    Listen, WaitingForKey, WaitForAck, DataExchange, Start, WaitingForAck
};

//----------------------------------------------------------------------------------------------

// test if there is enough bytes in the serial buffer within the given time
bool wait_on_serial3 (uint8_t nbytes, long timeout) {
    unsigned long deadline = millis() + timeout;
    while (Serial3.available() < nbytes && (timeout < 0 || millis() < deadline)) {
        delay(1);
    }
    return Serial3.available() >= nbytes;
}

//---------------------------------------------------------------------------------------------

//client function to perform handshake
uint32_t client_exchange(uint32_t& ckey, uint32_t& cmod, uint32_t& m) {
	//initiate client status and all variables used in the function
    StateNames clientstate = Start;
    uint32_t ACK;
    uint32_t skey, smod;

    // start data exchanging
     while (clientstate != DataExchange) {

     	// if the client is in the Start phase, it sends CR(ckey,cmod) to the server
        if (clientstate == Start) {
            Serial3.write('C');
            uint32_to_serial3(ckey);
            uint32_to_serial3(cmod);
            clientstate = WaitingForAck;
        }

        //if the client is in the WaitingForAck mode, after successfully reading the ACK, it stores the skey and smod after the ACK message
        if (clientstate == WaitingForAck) {
        	//determin if ACK is received within the given timeout.
            if (wait_on_serial3(9, 1000)) {
                ACK = Serial3.read();

                //if yes, store keys and send ACK to server; 
                if (ACK == 65) {
                    skey = uint32_from_serial3();
                    smod = uint32_from_serial3();
                    ckey = skey;
                    m = smod;
                    uint32_to_serial3(ACK);
                    clientstate = DataExchange;
                }

                //if not, go to the previous phase.
                else {
                    clientstate = Start;
                }
            }
            else {
                clientstate = Start;
            }
        }
    }
}

//--------------------------------------------------------------------------------------------

// server function to perform data exchange
uint32_t server_exchange(uint32_t& skey, uint32_t& smod, uint32_t& m) {
	// initiate the server state and all variables used in this function
    StateNames serverstate = Listen;
    uint32_t CR, ACK;
    uint32_t ckey, cmod;

    // start handshake process
    while (serverstate != DataExchange) {

    	//Listen for the CR(ckey, cmod) from the client
        if (serverstate == Listen) {
            if (Serial3.available() > 0) { 
                CR = Serial3.read();
                //Serial.println(CR);
            }

            // If the correct CR is received, go to the next stage
            if (CR == 67) serverstate = WaitingForKey;
        }

        //Store ckey and cmod which follow the CR, and send ACK(skey, smod)
        if (serverstate == WaitingForKey) {

        	// Determin if the ckey and cmod was passed to the buffer within the given timeout(1000ms). If yes, tore keys and send values
            if (wait_on_serial3(8, 1000)) {
                ckey = uint32_from_serial3();
                cmod = uint32_from_serial3();
                m = cmod;
                Serial3.write('A');
                uint32_to_serial3(skey);
                uint32_to_serial3(smod);
                serverstate = WaitForAck;
            }
            // if not, return to the beginning phase
            else{
                serverstate = Listen;
            }
        }

        // Determin whether the client has received the ACK(skey, smod)
        if (serverstate == WaitForAck) {

        	// Determin if an ACK is sent to the buffer by the client within the timeout provided
            if (wait_on_serial3(1, 1000)) {
                ACK = Serial3.read();

                // If an ACK is received, the handshake is complete. Change skey value.
                if (ACK == 65) {
                    serverstate = DataExchange;
                    skey = ckey;
                }
                // If an CR is received, go to the beginning phase.
                else if (ACK == 67) {
                    serverstate = WaitingForKey;
                }
            }
        }
    }
}

//--------------------------------------------------------------------------------------------
void communication(uint32_t d,uint32_t n,uint32_t e,uint32_t m){


    uint32_t original_info, encrypted_info, decrypted_info;

    if (Serial.available() > 0) {
        original_info = Serial.read();
        //If user type return charater then we encrypt it and send. We also write it on Serial too. This part is changed according to profs solution on eclass as in submission 1 our marks were deducted for this.
        if (original_info == 13){
            Serial.write('\r');
            uint32_to_serial3(encrypt('\r', e, m));
            Serial.write('\n');
            uint32_to_serial3(encrypt('\n', e, m));
        }
        else{
            Serial.write(original_info);
            encrypted_info = encrypt(original_info,e,m);

            //To write uint32_t to serial3 we send by spliting it into groups of 8 bits (1 byte) at a time.
            uint32_to_serial3(encrypted_info);
        }
    }

        //information is not recieved until its not more then 3 bytes. We want all 4 bytes to be availabe to start decoding them.
    if (Serial3.available() > 3) {

        encrypted_info = uint32_from_serial3();
        decrypted_info = decrypt(encrypted_info,d,n);
        Serial.write(decrypted_info);  
    }
}

//----------------------------------------------------------------------------------------------

int main() {
    setup();

    uint32_t d, n, e, m;

    // If pin 13 is connected to 5V then arduino act as a server.
    if (digitalRead(Pin) == HIGH){
        Serial.println("Arduino is set as a server!");
        find_keys_mod(d,n,e);
        server_exchange(e, n, m);
        
    }

    // If pin 13 is connected to GND then arduino act as a client.
    else if (digitalRead(Pin) == LOW){
    
        Serial.println("Arduino is set as a client!");
        find_keys_mod(d,n,e);
        client_exchange(e, n, m);
    }
    
    // The delay here is used to let the server and the client to finish the handshake process
    delay(25);

    // Restart the two serials to prepare them for the communication.
    Serial.end();
    Serial3.end();
    setup();

    // Start encrypted communication
    while (true) {
      	communication(d,n,e,m);
    }

    Serial.flush();

    return 0;
}

//----------------------------------------------------------------------------------------------
