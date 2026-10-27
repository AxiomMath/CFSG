module

public import CFSG.Monster.B.TwoA.Amalgam.NativeChain
public import CFSG.Monster.B.TwoA.Fischer.AmbientRootNative

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA

theorem native_distance_three_labels_commute_and_fix_endpoints_final
    {v u : CVert}
    (hvu : cgraph.dist v u = 3) :
    clabelS u ∈ vStab v ∧ clabelS v ∈ vStab u ∧ clabelS v ≠ clabelS u ∧
      clabelS v * clabelS v = 1 ∧ clabelS u * clabelS u = 1 ∧ clabelS v ≠ 1 ∧
      clabelS u ≠ 1 ∧ Commute (clabelS v) (clabelS u) ∧
      IsKleinFour (Subgroup.closure {clabelS v, clabelS u}) ∧
      Subgroup.closure {clabelS v, clabelS u} ≤ vStab v ⊓ vStab u ∧
      vStab v ⊓ vStab u ≤ vStab v ⊓ Subgroup.centralizer {clabelS u} :=
  native_distance_three_labels_commute_and_fix_endpoints
    (distThreePathFact_of_ambient ambientRootOrbitsHyp) (mem_sphereDistThree.2 hvu)

end CFSG.Monster.B.TwoA.Amalgam
