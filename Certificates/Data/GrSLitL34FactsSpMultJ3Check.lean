module

public import CFSG.Certificates.CosetTablePresented
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
public import Mathlib

public section

namespace CFSG.ComponentClassification.GSThmB.SpMult

abbrev j3Gens : ℕ := TauCeti.SporadicName.J3.presentation.generatorCount

abbrev j3Rels : List (List (Fin j3Gens × Bool)) := TauCeti.SporadicName.J3.presentation.relators

@[expose] def commWord {m : ℕ} (x r : List (Fin m × Bool)) : List (Fin m × Bool) :=
  FreeGroup.invRev x ++ FreeGroup.invRev r ++ x ++ r

@[expose] def centralWords {m : ℕ} (r : List (Fin m × Bool)) : List (List (Fin m × Bool)) :=
  (List.finRange m).map (fun x => commWord [(x, true)] r) ++ [r ++ r]

@[expose] def j3CoverRels : List (List (Fin j3Gens × Bool)) :=
  [j3Rels.getD 0 [], j3Rels.getD 1 [], j3Rels.getD 3 [], j3Rels.getD 4 [], j3Rels.getD 5 [],
    j3Rels.getD 7 []] ++ centralWords (j3Rels.getD 2 []) ++ centralWords (j3Rels.getD 6 [])

end CFSG.ComponentClassification.GSThmB.SpMult
