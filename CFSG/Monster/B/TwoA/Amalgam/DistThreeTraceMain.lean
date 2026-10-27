module

public import CFSG.Monster.B.TwoA.Amalgam.DistThreeTraceBase

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA

theorem native_distance_three_labels_commute_and_fix_endpoints
    (hX : DistThreePathFact)
    {v u : CVert} (hvu : u ∈ sphereDistThree v) :
    clabelS u ∈ vStab v ∧ clabelS v ∈ vStab u ∧ clabelS v ≠ clabelS u ∧
      clabelS v * clabelS v = 1 ∧ clabelS u * clabelS u = 1 ∧ clabelS v ≠ 1 ∧
      clabelS u ≠ 1 ∧ Commute (clabelS v) (clabelS u) ∧
      IsKleinFour (Subgroup.closure {clabelS v, clabelS u}) ∧
      Subgroup.closure {clabelS v, clabelS u} ≤ vStab v ⊓ vStab u ∧
      vStab v ⊓ vStab u ≤ vStab v ⊓ Subgroup.centralizer {clabelS u} :=
  native_distance_three_labels_commute_and_fix_endpoints_of hX distThreeBaseTransvFact_holds hvu

theorem distThree_labels_of_pathFact
    (hX : DistThreePathFact) (v u : CVert)
    (hvu : cgraph.dist v u = 3) :
    clabelS u ∈ vStab v ∧ clabelS v ∈ vStab u ∧ clabelS u ≠ clabelS v ∧
      Commute (clabelS u) (clabelS v) := by
  obtain ⟨h1, h2, hne, -, -, -, -, hc, -⟩ :=
    native_distance_three_labels_commute_and_fix_endpoints hX (v := v) (u := u) hvu
  exact ⟨h1, h2, Ne.symm hne, hc.symm⟩

end CFSG.Monster.B.TwoA.Amalgam
