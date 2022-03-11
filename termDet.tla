-------------------- MODULE termDet -------------------
EXTENDS Integers, Sequences, FiniteSets, TLC
CONSTANT N, MaxT
ASSUME N \in Nat \ {0,1}
Procs == 1..N

(* 
--algorithm termDet {
  variables
  chan = [n \in 0..N |-> <<>>];  \* FIFO channels 


  macro send(des, msg) {
      chan[des] := Append(chan[des], msg);
  }

  macro receive(msg) {
      when Len(chan[self]) > 0;
      msg := Head(chan[self]);
      chan[self] := Tail(chan[self]);
  }


  fair process (j \in Procs)
  variables
  T=0;
  m=0;
  active=TRUE;
  inc  =0;
  outc = [n \in 1..N |-> 0];
  {
P:    while (T < MaxT){  
        T := T+1;
        \* Write the code for the actions using either or 
          either 
Receive:   { \* receive event
             inc := inc + 1;
             active := TRUE;
             receive(m);
            };
          or
Send:      { \* send event
             await(active = TRUE); 
             with (k \in Procs){
                send(k,m);
                outc[k]:= outc[k] + 1;
             };
            };            
          or
Idle:      {\* notify idle to detector
            await (active = TRUE);
            active := FALSE;
            
            \* Notifiying the detector
            send(0,<<self,inc,outc>>);
            
            \* Resetting the counters
            inc:= 0;
            outc:= [n \in 1..N |-> 0]; 
            };            
      }
  }


  fair process (d \in {0}) \* Detector process
  variables
  id = 0;
  done=FALSE;
  msg= <<>>;
  notified={};
  j=1;
  outS = [n \in 1..N |-> 0];
  inS = [n \in 1..N |-> 0];
  {
D:  while(~done) {
        receive(msg);
        
        \* Adding the process ID received in the msg to notified set
        notified := notified \union {msg[1]};
        
        \* Updating the total inS count for the process ID received
        inS[msg[1]] := msg[2];
        
        \* Updating the outS count for the each of the outgoing channels from process ID received
        outS := [k \in 1..N |-> outS[k] + msg[3][k]];
        
        \* Checking for termination
        if ((\A k \in Procs: k \in notified) /\ (inS = outS)){
            done := TRUE;
        }
      }     
    } 
  }

}
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-71032d6bd8d9ec0ecd1a7681c2821945
\* Process j at line 24 col 8 changed to j_
VARIABLES chan, pc, T, m, active, inc, outc, id, done, msg, notified, j, outS, 
          inS

vars == << chan, pc, T, m, active, inc, outc, id, done, msg, notified, j, 
           outS, inS >>

ProcSet == (Procs) \cup ({0})

Init == (* Global variables *)
        /\ chan = [n \in 0..N |-> <<>>]
        (* Process j_ *)
        /\ T = [self \in Procs |-> 0]
        /\ m = [self \in Procs |-> 0]
        /\ active = [self \in Procs |-> TRUE]
        /\ inc = [self \in Procs |-> 0]
        /\ outc = [self \in Procs |-> [n \in 1..N |-> 0]]
        (* Process d *)
        /\ id = [self \in {0} |-> 0]
        /\ done = [self \in {0} |-> FALSE]
        /\ msg = [self \in {0} |-> <<>>]
        /\ notified = [self \in {0} |-> {}]
        /\ j = [self \in {0} |-> 1]
        /\ outS = [self \in {0} |-> [n \in 1..N |-> 0]]
        /\ inS = [self \in {0} |-> [n \in 1..N |-> 0]]
        /\ pc = [self \in ProcSet |-> CASE self \in Procs -> "P"
                                        [] self \in {0} -> "D"]

P(self) == /\ pc[self] = "P"
           /\ IF T[self] < MaxT
                 THEN /\ T' = [T EXCEPT ![self] = T[self]+1]
                      /\ \/ /\ pc' = [pc EXCEPT ![self] = "Receive"]
                         \/ /\ pc' = [pc EXCEPT ![self] = "Send"]
                         \/ /\ pc' = [pc EXCEPT ![self] = "Idle"]
                 ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                      /\ T' = T
           /\ UNCHANGED << chan, m, active, inc, outc, id, done, msg, notified, 
                           j, outS, inS >>

Receive(self) == /\ pc[self] = "Receive"
                 /\ inc' = [inc EXCEPT ![self] = inc[self] + 1]
                 /\ active' = [active EXCEPT ![self] = TRUE]
                 /\ Len(chan[self]) > 0
                 /\ m' = [m EXCEPT ![self] = Head(chan[self])]
                 /\ chan' = [chan EXCEPT ![self] = Tail(chan[self])]
                 /\ pc' = [pc EXCEPT ![self] = "P"]
                 /\ UNCHANGED << T, outc, id, done, msg, notified, j, outS, 
                                 inS >>

Send(self) == /\ pc[self] = "Send"
              /\ (active[self] = TRUE)
              /\ \E k \in Procs:
                   /\ chan' = [chan EXCEPT ![k] = Append(chan[k], m[self])]
                   /\ outc' = [outc EXCEPT ![self][k] = outc[self][k] + 1]
              /\ pc' = [pc EXCEPT ![self] = "P"]
              /\ UNCHANGED << T, m, active, inc, id, done, msg, notified, j, 
                              outS, inS >>

Idle(self) == /\ pc[self] = "Idle"
              /\ (active[self] = TRUE)
              /\ active' = [active EXCEPT ![self] = FALSE]
              /\ chan' = [chan EXCEPT ![0] = Append(chan[0], (<<self,inc[self],outc[self]>>))]
              /\ inc' = [inc EXCEPT ![self] = 0]
              /\ outc' = [outc EXCEPT ![self] = [n \in 1..N |-> 0]]
              /\ pc' = [pc EXCEPT ![self] = "P"]
              /\ UNCHANGED << T, m, id, done, msg, notified, j, outS, inS >>

j_(self) == P(self) \/ Receive(self) \/ Send(self) \/ Idle(self)

D(self) == /\ pc[self] = "D"
           /\ IF ~done[self]
                 THEN /\ Len(chan[self]) > 0
                      /\ msg' = [msg EXCEPT ![self] = Head(chan[self])]
                      /\ chan' = [chan EXCEPT ![self] = Tail(chan[self])]
                      /\ notified' = [notified EXCEPT ![self] = notified[self] \union {msg'[self][1]}]
                      /\ inS' = [inS EXCEPT ![self][msg'[self][1]] = msg'[self][2]]
                      /\ outS' = [outS EXCEPT ![self] = [k \in 1..N |-> outS[self][k] + msg'[self][3][k]]]
                      /\ IF (\A k \in Procs: k \in notified'[self]) /\ (inS'[self] = outS'[self])
                            THEN /\ done' = [done EXCEPT ![self] = TRUE]
                            ELSE /\ TRUE
                                 /\ done' = done
                      /\ pc' = [pc EXCEPT ![self] = "D"]
                 ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                      /\ UNCHANGED << chan, done, msg, notified, outS, inS >>
           /\ UNCHANGED << T, m, active, inc, outc, id, j >>

d(self) == D(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Procs: j_(self))
           \/ (\E self \in {0}: d(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars(j_(self))
        /\ \A self \in {0} : WF_vars(d(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-73e74abd9de44dfb6f804fbacfd1c6d5

Safety   ==  (done[0] => (\A self \in Procs: (active[self] = FALSE /\ chan[self] = <<>>)))\* remove the leftmost comment sign and fill the Safety Property after == 
Progress == (\A self \in Procs: (active[self] = FALSE /\ chan[self] = <<>>)) ~> done[0] \* remove the leftmost comment sign and fill the Progress property 

==================================================

\* Include the team member names here 
Upasana Ghosh (UB Person #50317396)
Sriparna Chakraborty (UB Person #50314303)

PART 2
Modified Termination Detection Algorithm :
(Each process keeps track of the total messages sent per channel and a count of the total messages received)

MODIFICATION :

In the previous termination detection algorithm (i.e, part 1 of the project), we implemented the algorithm
in a way such that, each process maintained two local counters -
i) inc: an integer value maintaining the total incoming messages that it received
ii) outc: an integer value maintaining the total outgoing messages that it sent

The main flaw in this algorithm was with respect to the way we were maintaining these counters. To decide whether the system has
reached termination, the detector process checked if the total sum of messages received by all processes in the system was equal
to the total messages sent by all the processes in the system, irrespective of the channels. But this is not enough information
to determine system termination correctly. 

To resolve this issue, in the modified version of the termination algorithm, 

i) At each process, we keep a set of counters for the outgoing messages per channel (each channel connecting the process to all
the other processes in the system), i.e, we modify the outc from an integer value to a vector. We keep the incoming message counter
as it is, i.e, inc is kept as a integer value as we only need to consider the total messages received at a process from all the
channels while determining termination at detector process.

ii) In the detector process, we update the counters for maintaining the total outgoing messages (outS) and total incoming messages
in system (inS), from an integer value to a vector i.e, we now maintain a count of incoming and outgoing messages for each process
(or, each channel). 

iii) While notifying the detector process, now each process will send its local count of all incoming messages and a vector of count
of total messages that it has sent out in each channel(or, to each of the other processes).

iv) On receiving an idle notification from a process, the detector now updates it local counter with the incoming message count for
that particular process in it's inS set and updates all the values in the outS set with the counts received in the outc set of that
process.

This way, while checking for system termination, the detector process ensures that it has received an idle mesage atleast once from 
each of the processes, as well as it ensures that each message sent over a particular channel is also recieved correctly. In other 
words, it ensures that when the system terminates, all the processes are idle and all the channels are empty. Hence, correctly terming
when a system terminates.

SAFETY PROPERTY AND ITS CORRECTNESS CHECKING:

The safety property for our program is:

Safety   ==  (done[0] => (\A k \in Procs: (active[k] = FALSE /\ chan[k] = <<>>)))

Termination is a stable property. So, to prove safety, we need to show that the state just seen by the detector(when done sets to TRUE) is a valid snapshot.
When done is True, this indicates that the detector has received information from all the processes. By information, we mean the message tuple that each process 
sends <<id,inc,outc>> when it wants to be in the Idle state. Formally, for this computation to be a valid snapshot,i.e., a consistent cut, 
it should be shown for each channel c that:
(\A c:: send.c >= receive.c), 
because the detector has some past cut information.

But for termination detection, this particular cut can be considered as a valid snapshot only when (\A c:: send.c = receive.c).
To ensure that we end up having a valid snapshot when the computation ends, we keep the check:

\* Checking for termination
        if ((\A k \in Procs: k \in notified) /\ (inS = outS)){
            done := TRUE;
            
i.e., the detector’s flag ‘done’ sets to true and the computation exits the while loop and terminates only when for all processes k fro
m 1..N, k is in the notified set, i.e. the detector is aware of its transition to idle state and for each process, count of inS and outS across each channel 
should be equal i.e., all the channels are empty.This shows that for the second part of the program, safety property holds throughout its execution. 
In other words,it can also be said that once the program enters this terminated state, the state of the program does not change.

PROGRESS PROPERTY AND ITS CORRECTNESS CHECKING:

The progress property for our program is:

Progress == (\A k \in Procs: (active[k] = FALSE /\ chan[k] = <<>>)) ~> done[0]
To prove this, we need to show that when all processes are idle and the channel for each process is empty i.e., counts of sent messages and received 
messages across each channel are equal, termination is eventually achieved. We implemented this in the code by providing the following condition:

if ((\A k \in Procs: k \in notified) /\ (inS = outS)){
            done := TRUE;
            

Thus, when all the processes notify the detector about their transition to the Idle state ie., they are all in the notified set and send.c = receive.c, 
done is set to True, i.e., eventually the flag is set to True for the detector and the computation terminates.
