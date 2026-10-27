module

public import CFSG.GH74.KGroups.L34Inputs
public import CFSG.GH74.KGroups.PermCheck
public meta import CFSG.GH74.KGroups.L34Inputs
public meta import CFSG.GH74.KGroups.PermCheck

public section

namespace CFSG.RankThree.PartTwo.KFacts.L34Max

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.GH74.KGroups CFSG.GH74.KGroups.L34

@[expose] def ofPAB (w : List ℤ) : Equiv.Perm (Fin 21) := tab (evalCodes [pa, pb] w)

@[expose] def n0a : Equiv.Perm (Fin 21) :=
  ofPAB [1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 2]

@[expose] def n0b : Equiv.Perm (Fin 21) := ofPAB [1, 2, 1, 2, 1, 2, 2, 2, 1, 2, 1, 2, 2, 2]

@[expose] def e0a : Equiv.Perm (Fin 21) :=
  ofPAB [2, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 2]

@[expose] def e0b : Equiv.Perm (Fin 21) := ofPAB [1, 2, 2, 1, 2, 2, 2, 1, 2, 1, 2, 2, 2, 1, 2]

@[expose] def QN0 : RawSchreierDatum 21 :=
  certificate (by decide) [n0a, n0b] [[1, 1, 2, 1]] #v[2, 3] (by decide)

@[expose] def QE0 : RawSchreierDatum 21 :=
  certificate (by decide) [e0a, e0b] [] #v[2] (by decide)

@[expose] def U0 : Finset (Fin 21) := {2, 3, 4, 6, 7, 8, 9, 13, 17}

@[expose] def keyF (g : Equiv.Perm (Fin 21)) : Finset (Fin 21) := U0.image g

@[expose] def repData : List (List ℤ × List ℤ × List ℤ) :=
  [([2, 1, 2, 1, 2], [3, 1, 2, 1, 1, 1, 3], [1, 1, 1, 3, 3, 1, 2, 3, 3, 1]),
   ([2, 1, 2, 2, 1, 2], [2, 2, 3, 3, 1, 1, 1, 2, 3], [1, 1, 2, 2, 3, 2, 3, 3, 2, 3, 2]),
   ([2, 1, 2], [2, 2, 3, 1, 2, 1, 2, 2, 3, 1], [1, 2, 3, 2, 3, 2, 1, 3, 3, 1]),
   ([2, 1, 2, 1, 2, 2], [2, 1, 3, 1, 3, 3, 1, 1, 2, 2], [1, 3, 1, 3, 3, 1, 3, 3, 1, 3]),
   ([2, 2, 1, 2, 1, 2], [1, 3, 3, 1, 3, 3, 1], [1, 3, 1, 1, 3, 1, 2, 3, 3, 1, 2]),
   ([1], [3], [1, 2, 3, 1, 1, 1, 3]),
   ([2], [2, 2, 1, 1, 1, 3, 1, 3, 3, 2], [3])]

@[expose] def reps : List (Equiv.Perm (Fin 21)) := repData.map fun d => ofPAB d.1

@[expose] def targets : List (Finset (Fin 21)) :=
  (elemsT QN0).flatMap fun n => reps.map fun g => keyF (n * g)

@[expose] def normCheck : Bool :=
  [n0a, n0b].all fun n => [e0a, e0b].all fun e => QE0.sift (n * e * n⁻¹) 0

@[expose] def outCheck : Bool := !(QE0.sift (pa * e0a * pa⁻¹) 0)

@[expose] def genCheck : Bool :=
  repData.all fun d =>
    schreierPermEq (evalCodes [n0a, n0b, ofPAB d.1] d.2.1) pa &&
      schreierPermEq (evalCodes [n0a, n0b, ofPAB d.1] d.2.2) pb

@[expose] def stabCheck : Bool :=
  (elemsT QP21).all fun y => if keyF y = U0 then QN0.sift y 0 else targets.contains (keyF y)

end CFSG.RankThree.PartTwo.KFacts.L34Max
