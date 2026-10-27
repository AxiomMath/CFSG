
module

public import CFSG.Sporadic.Schreier.PairMcLCertBase
public meta import CFSG.Sporadic.Schreier.PairMcLCertBase
public meta import Certificates.Data.CFSGNative.PairSchreier.Core
public meta import Certificates.Data.CFSGNative.Schreier.Check
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain

public section

namespace CFSG.Sporadic.Schreier.PairMcL

open CFSG.Sporadic.Schreier.PairNative CFSG.Certificates.Native CFSG.Monster.B.Co2.Native

@[expose] def baseArr : Array Nat := #[0, 1, 2, 3, 4]

@[expose] def bs : List Nat := [0, 1, 2, 3, 4]

@[expose] def levels : Array Level := rawLevels 275 mclStrongArrs baseArr

@[expose] def gens : Array (Array Nat) := #[mclStrongArrs[0]!, mclStrongArrs[1]!]

@[expose] def gensInv : Array (Array Nat) :=
  #[(rawInvs 275 mclStrongArrs)[0]!, (rawInvs 275 mclStrongArrs)[1]!]

@[expose] def wA : List (Array Nat) := [mclStrongArrs[0]!]

@[expose] def wB : List (Array Nat) := [mclStrongArrs[1]!]

@[expose] def commPat : List Bool := [false, true, false, true, true, true, true]

@[expose] def closureOf (w : List (Array Nat)) : Array (Array Nat) × Array Nat × Array Nat :=
  conjClosureNF 275 levels bs gens gensInv (decodeNF levels (baseImgs bs w).toArray) 30000

@[expose] def cl : List (List (Array Nat) × Array (Array Nat) × Array Nat × Array Nat) :=
  [wA].map fun w => (w, closureOf w)

end CFSG.Sporadic.Schreier.PairMcL
