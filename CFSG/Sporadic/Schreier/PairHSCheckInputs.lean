module

public import CFSG.Sporadic.Schreier.PairHSCert
public meta import CFSG.Sporadic.Schreier.PairHSCert
public meta import Certificates.Data.CFSGNative.PairSchreier.Core
public meta import Certificates.Data.CFSGNative.Schreier.Check
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain

public section

namespace CFSG.Sporadic.Schreier.PairHS

open CFSG.Sporadic.Schreier.PairNative CFSG.Certificates.Native CFSG.Monster.B.Co2.Native

@[expose] def baseArr : Array Nat := #[0, 1, 2, 3]

@[expose] def bs : List Nat := [0, 1, 2, 3]

@[expose] def levels : Array Level := rawLevels 3850 hsStrongArrs baseArr

@[expose] def gens : Array (Array Nat) := #[hsStrongArrs[0]!, hsStrongArrs[1]!]

@[expose] def gensInv : Array (Array Nat) :=
  #[(rawInvs 3850 hsStrongArrs)[0]!, (rawInvs 3850 hsStrongArrs)[1]!]

@[expose] def wA : List (Array Nat) := [hsStrongArrs[0]!]

@[expose] def wB : List (Array Nat) := [hsStrongArrs[1]!]

@[expose] def commPat : List Bool := [false, true, false, true, true, true, true]

@[expose] def wC : List (Array Nat) := (List.replicate 5 (patW wA wB [false, true, true])).flatten

@[expose] def closureOf (w : List (Array Nat)) : Array (Array Nat) × Array Nat × Array Nat :=
  conjClosureNF 3850 levels bs gens gensInv (decodeNF levels (baseImgs bs w).toArray) 20000

@[expose] def cl : List (List (Array Nat) × Array (Array Nat) × Array Nat × Array Nat) :=
  [wA, wC].map fun w => (w, closureOf w)

end CFSG.Sporadic.Schreier.PairHS
