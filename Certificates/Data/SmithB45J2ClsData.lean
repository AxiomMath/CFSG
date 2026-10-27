module

public import CFSG.Sporadic.Schreier.PairJ2CheckInputs
public import Certificates.Data.CFSGNative.PairSchreier.Counts
public meta import CFSG.Sporadic.Schreier.PairJ2CheckInputs
public meta import Certificates.Data.CFSGNative.PairSchreier.Core
public meta import Certificates.Data.CFSGNative.PairSchreier.Counts

public section

namespace CFSG.Quasithin.J2Cls

open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative

@[expose] def p15A : List Bool :=
  [true, true, false, true, false, true, true, false, true, true, false, true, false, true, false,
    true, true, false, true, false, true, true, false, true, false, true, false]

@[expose] def p15B : List Bool :=
  [true, true, false, true, true, false, true, false, true, true, false, true, false, true, false,
    true, true, false, true, false, true, true, false, true, false, true, false]

@[expose] def p5C : List Bool :=
  [true, true, false, true, true, false, true, false, true, false, true, true, false, true, false,
    true, true, false, true, false, true, false, true, true, false, true, false, true, false]

@[expose] def p5D : List Bool :=
  [true, true, false, true, false, true, true, false, true, false, true, false, true, true, false,
    true, true, false, true, false, true, false, true, true, false, true, false, true, false]

@[expose] def w15A : List (Array Nat) := patW PairJ2.wA PairJ2.wB p15A

@[expose] def w15B : List (Array Nat) := patW PairJ2.wA PairJ2.wB p15B

@[expose] def w5C : List (Array Nat) := patW PairJ2.wA PairJ2.wB p5C

@[expose] def w5D : List (Array Nat) := patW PairJ2.wA PairJ2.wB p5D

@[expose] def w7 : List (Array Nat) := patW PairJ2.wA PairJ2.wB [false, true]

@[expose] def w3A : List (Array Nat) := (List.replicate 5 w15A).flatten

@[expose] def w5A : List (Array Nat) := (List.replicate 3 w15A).flatten

@[expose] def w5B : List (Array Nat) := (List.replicate 6 w15A).flatten

@[expose] def oddReps : List (List (Array Nat) × Nat) :=
  [(w3A, 3), (PairJ2.wB, 3), (w5A, 5), (w5B, 5), (w5C, 5), (w5D, 5), (w7, 7), (w15A, 15),
    (w15B, 15)]

@[expose] def closureOf (w : List (Array Nat)) : Array (Array Nat) × Array Nat × Array Nat :=
  conjClosureNF 315 PairJ2.levels PairJ2.bs PairJ2.gens PairJ2.gensInv
    (decodeNF PairJ2.levels (baseImgs PairJ2.bs w).toArray) 100000

@[expose] def oddCl : List (List (Array Nat) × Array (Array Nat) × Array Nat × Array Nat) :=
  oddReps.map fun r => (r.1, closureOf r.1)

end CFSG.Quasithin.J2Cls
