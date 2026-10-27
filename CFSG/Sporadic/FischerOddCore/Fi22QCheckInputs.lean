module

public import CFSG.Sporadic.FischerOddCore.Fi22SylowCheck
public import CFSG.Sporadic.FischerOddCore.Fi22CTICheckInputs
public meta import CFSG.Sporadic.FischerOddCore.Fi22SylowCheck
public meta import CFSG.Sporadic.FischerOddCore.Fi22CTICheckInputs

public section

namespace CFSG.Sporadic.FischerOddCore

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Monster.B.Fischer
open CFSG.Sporadic.FischerOddCore.Native

@[expose] def fi22QG (c k : Nat) : Array Nat := fi22CentArr (fi22CentStrongStart.getD c 0 + k)

@[expose] def fi22QGi (c k : Nat) : Array Nat := invCand 3510 (fi22QG c k)

@[expose] def fi22QArr (c : Nat) (seed : Array Nat) (steps : List (Nat × Nat)) :
    Array (Array Nat) :=
  steps.foldl (fun Q st => Q.push (conjArr 3510 (fi22QG c st.1) (fi22QGi c st.1) Q[st.2]!)) #[seed]

@[expose] def fi22QOK (c : Nat) (Q : Array (Array Nat)) (N : Nat) (ss : List Nat)
    (E : Array (Array Nat)) (par gen nxt : Array Nat) : Bool :=
  let Ls := rawLevels 3510 (fi22CentStrong c) #[0, 1, 2, 3, 6, 4]
  closureOK 3510 Q E par gen nxt && E.size == N && keysOK 3510 [0, 1, 2, 3, 6, 4] E &&
    allLt Q.size (fun j => isInvA 3510 Q[j]! (invCand 3510 Q[j]!)) &&
    allLt Q.size (fun j => siftA 3510 Ls #[0, 1, 2, 3, 6, 4] 0 Q[j]!) &&
    allLt (fi22CentGenCount.getD c 0) (fun k => allLt Q.size fun j =>
      ctiMem E (conjArr 3510 (fi22QG c k) (fi22QGi c k) Q[j]!)) &&
    ss.all fun s =>
      let W := fi22SylWits s
      allLt (fi22CentSylowField s 7) fun w =>
        !(eqA 3510 (compA 3510 W[w]! Q[0]!) (compA 3510 Q[0]! W[w]!))

@[expose] def fi22QChecks (c : Nat) (Q : Array (Array Nat)) (N : Nat) (ss : List Nat) : Bool :=
  let r := closureSearch 3510 Q (N + 1)
  fi22QOK c Q N ss r.1 r.2.1 r.2.2.1 r.2.2.2

@[expose] def fi22QTwoArr : Array (Array Nat) :=
  fi22QArr 2 (Native.powA 3510 (compA 3510 (fi22QG 2 0) (fi22QG 2 1)) 10)
    [(2, 0), (0, 1), (1, 1), (2, 2), (0, 3)]

@[expose] def fi22QZeroArr : Array (Array Nat) :=
  fi22QArr 0 (Native.powA 3510 (compA 3510 (fi22QG 0 0) (fi22QG 0 5)) 4)
    [(1, 0), (2, 0), (3, 0), (4, 0), (6, 0), (8, 0), (9, 0), (11, 0)]

end CFSG.Sporadic.FischerOddCore
