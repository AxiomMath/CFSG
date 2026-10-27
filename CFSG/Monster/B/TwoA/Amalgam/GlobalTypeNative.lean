module

public import CFSG.Monster.B.TwoA.Amalgam.GlobalTypeRemain
public import CFSG.Monster.B.TwoA.Amalgam.FischerNodes

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA

theorem fischer_126_neighbor_orbit_globally_type_three_of_ambient
    (hamb : AmbientRootOrbitsHyp)
    {v w : CVert} (hw : w ∈ sphereThree v) : outerOrbit v w 694980 ⊆ sphereThree v :=
  fischer_126_neighbor_orbit_globally_type_three_of hamb
    (fun v w hw => (native_Fischer_maximal_clique_stabilizer_kernel v w hw).1) hw

theorem fischer_remaining_orbit_global_types_of_ambient
    (hamb : AmbientRootOrbitsHyp) :
    (∀ v w : CVert, w ∈ sphereThree v →
      outerOrbit v w 142155 ∪ outerOrbit v w 694980 ⊆ sphereThree v ∧
        outerOrbit v w 3127410 ⊆ sphereFour v) ∧
    ∀ v w : CVert, w ∈ sphereFour v → ∀ Ω : Fin 8 → Set CVert,
      (∀ i, Ω i ⊆ cgraph.neighborSet v) → (∀ u ∈ cgraph.neighborSet v, ∃! i, u ∈ Ω i) →
      (∀ i, ∀ u ∈ Ω i, {x | ∃ y ∈ vStab v ⊓ vStab w, cvMul u y = x} = Ω i) →
      (∀ i, (Ω i).ncard = ![648, 8064, 663552, 1, 1134, 36288, 1161216, 2097152] i) →
      cgraph.neighborSet v ∩ sphereThree w = Ω 2 :=
  fischer_remaining_orbit_global_types_of hamb
    fun v w hw => (native_Fischer_maximal_clique_stabilizer_kernel v w hw).1

end CFSG.Monster.B.TwoA.Amalgam
