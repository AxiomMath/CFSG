module

public import CFSG.Sporadic.HeldB.HeBlocks
public meta import CFSG.Sporadic.HeldB.HeBlocks
public meta import CFSG.Sporadic.HeldB.CertPChainData
public meta import Certificates.Data.CFSGNative.PairSchreier.Core
public meta import Certificates.Data.CFSGNative.Schreier.Check
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain

public section

namespace CFSG.Sporadic.Schreier.PairHe

open CFSG.Sporadic.Schreier.PairNative CFSG.Certificates.Native CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.HeldB

@[expose] def bs : List Nat := [0, 1, 2, 3, 4]

@[expose] def levels : Array Level := rawLevels 8330 heStrongArrs heBase.toArray

@[expose] def gens : Array (Array Nat) := #[heGen 0, heGen 1]

@[expose] def gensInv : Array (Array Nat) := #[invCand 8330 (heGen 0), invCand 8330 (heGen 1)]

@[expose] def wA : List (Array Nat) := [heGen 0]

@[expose] def wB : List (Array Nat) := [heGen 1]

@[expose] def commPat : List Bool := [false, true, false, true, true, true, true, true, true]

@[expose] def pat12 : List Bool := [false, true, true]

@[expose] def pat15 : List Bool := [false, true, false, true, true]

@[expose] def wT : List (Array Nat) :=
  (List.replicate 4 (patW wA wB [false, true, true, true])).flatten

@[expose] def closureOf (w : List (Array Nat)) : Array (Array Nat) × Array Nat × Array Nat :=
  conjClosureNF 8330 levels bs gens gensInv (decodeNF levels (baseImgs bs w).toArray) 200000

@[expose] def cl : List (List (Array Nat) × Array (Array Nat) × Array Nat × Array Nat) :=
  [wA, wT].map fun w => (w, closureOf w)

end CFSG.Sporadic.Schreier.PairHe
