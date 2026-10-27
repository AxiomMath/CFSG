module

public import Certificates.Data.CFSGNative.PairSchreier.Core
public import Certificates.Data.CFSGNative.PairSchreier.J2Data
public import Certificates.Data.CFSGNative.Schreier.Check
public meta import Certificates.Data.CFSGNative.PairSchreier.Core
public meta import Certificates.Data.CFSGNative.PairSchreier.J2Data
public meta import Certificates.Data.CFSGNative.Schreier.Check

public section

namespace CFSG.Sporadic.Schreier.PairJ2

open CFSG.Sporadic.Schreier.PairNative CFSG.Certificates.Native CFSG.Monster.B.Co2.Native

@[expose] def baseArr : Array Nat := #[1, 0, 2]

@[expose] def bs : List Nat := [1, 0, 2]

@[expose] def levels : Array Level := rawLevels 315 j2StrongArrs baseArr

@[expose] def groups : List (List Nat) := [[0], [1, 2]]

@[expose] def blocks : List (Array (Array Nat)) := blocksOf 315 levels groups

@[expose] def gens : Array (Array Nat) := #[j2StrongArrs[0]!, j2StrongArrs[1]!]

@[expose] def gensInv : Array (Array Nat) :=
  #[(rawInvs 315 j2StrongArrs)[0]!, (rawInvs 315 j2StrongArrs)[1]!]

@[expose] def wA : List (Array Nat) := [j2StrongArrs[0]!]

@[expose] def wB : List (Array Nat) := [j2StrongArrs[1]!]

@[expose] def commPat : List Bool := [false, true, false, true, true]

@[expose] def conds : List (List Bool × Nat) := [([false, true], 7), (commPat, 12)]

@[expose] def reps : List (List (Array Nat)) :=
  [wA, (List.replicate 6 (patW wA wB commPat)).flatten]

@[expose] def closureOf (w : List (Array Nat)) : Array (Array Nat) × Array Nat × Array Nat :=
  conjClosureNF 315 levels bs gens gensInv (decodeNF levels (baseImgs bs w).toArray) 3000

@[expose] def cl : List (List (Array Nat) × Array (Array Nat) × Array Nat × Array Nat) :=
  reps.map fun w => (w, closureOf w)

end CFSG.Sporadic.Schreier.PairJ2
