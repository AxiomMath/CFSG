
module

public import CFSG.Sporadic.Schreier.PairJ3CertBase
public meta import CFSG.Sporadic.Schreier.PairJ3CertBase
public meta import Certificates.Data.CFSGNative.PairSchreier.Core
public meta import Certificates.Data.CFSGNative.Schreier.Check
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain

public section

namespace CFSG.Sporadic.Schreier.PairJ3

open CFSG.Sporadic.Schreier.PairNative CFSG.Certificates.Native CFSG.Monster.B.Co2.Native

@[expose] def baseArr : Array Nat := #[0, 1, 3, 2]

@[expose] def bs : List Nat := [0, 1, 3, 2]

@[expose] def levels : Array Level := rawLevels 6156 j3StrongArrs baseArr

@[expose] def gens : Array (Array Nat) := #[j3StrongArrs[0]!, j3StrongArrs[1]!]

@[expose] def gensInv : Array (Array Nat) :=
  #[(rawInvs 6156 j3StrongArrs)[0]!, (rawInvs 6156 j3StrongArrs)[1]!]

@[expose] def wA : List (Array Nat) := [j3StrongArrs[0]!]

@[expose] def wB : List (Array Nat) := [j3StrongArrs[1]!]

@[expose] def commPat : List Bool := [false, true, false, true, true]

@[expose] def closureOf (w : List (Array Nat)) : Array (Array Nat) × Array Nat × Array Nat :=
  conjClosureNF 6156 levels bs gens gensInv (decodeNF levels (baseImgs bs w).toArray) 30000

@[expose] def cl : List (List (Array Nat) × Array (Array Nat) × Array Nat × Array Nat) :=
  [wA].map fun w => (w, closureOf w)

end CFSG.Sporadic.Schreier.PairJ3
