module

public import CFSG.Monster.B.TwoA.Amalgam.GlobalTypeNative
public import CFSG.Monster.B.TwoA.Fischer.AmbientRootNative

public section

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA

theorem fischer_126_neighbor_orbit_globally_type_three
    {v w : CVert} (hw : w ∈ sphereThree v) :
    outerOrbit v w 694980 ⊆ sphereThree v :=
  fischer_126_neighbor_orbit_globally_type_three_of_ambient ambientRootOrbitsHyp hw

theorem fischer_remaining_orbit_global_types :
    (∀ v w : CVert, w ∈ sphereThree v →
      outerOrbit v w 142155 ∪ outerOrbit v w 694980 ⊆ sphereThree v ∧
        outerOrbit v w 3127410 ⊆ sphereFour v) ∧
    ∀ v w : CVert, w ∈ sphereFour v → ∀ Ω : Fin 8 → Set CVert,
      (∀ i, Ω i ⊆ cgraph.neighborSet v) → (∀ u ∈ cgraph.neighborSet v, ∃! i, u ∈ Ω i) →
      (∀ i, ∀ u ∈ Ω i, {x | ∃ y ∈ vStab v ⊓ vStab w, cvMul u y = x} = Ω i) →
      (∀ i, (Ω i).ncard = ![648, 8064, 663552, 1, 1134, 36288, 1161216, 2097152] i) →
      cgraph.neighborSet v ∩ sphereThree w = Ω 2 :=
  fischer_remaining_orbit_global_types_of_ambient ambientRootOrbitsHyp

theorem native_type_three_neighborhood_global_distance_bound
    {v w : CVert}
    (hw : w ∈ sphereThree v) :
    cgraph.neighborSet w \ cgraph.commonNeighbors v w =
        outerOrbit v w 142155 ∪ outerOrbit v w 694980 ∪ outerOrbit v w 3127410 ∧
    {O | ∃ u ∈ cgraph.neighborSet w \ cgraph.commonNeighbors v w, O = pairStabOrbit v w u} =
        {outerOrbit v w 142155, outerOrbit v w 694980, outerOrbit v w 3127410} ∧
    (∀ n : ℕ, ∀ u ∈ outerOrbit v w n, pairStabOrbit v w u = outerOrbit v w n) ∧
    (outerOrbit v w 142155).ncard = 142155 ∧ (outerOrbit v w 694980).ncard = 694980 ∧
    (outerOrbit v w 3127410).ncard = 3127410 ∧
    (∀ u ∈ outerOrbit v w 142155,
      (cgraph.neighborSet u ∩ cgraph.commonNeighbors v w).ncard = 22) ∧
    (∀ u ∈ outerOrbit v w 694980,
      (cgraph.neighborSet u ∩ cgraph.commonNeighbors v w).ncard = 126) ∧
    (∀ u ∈ outerOrbit v w 3127410,
      (cgraph.neighborSet u ∩ cgraph.commonNeighbors v w).ncard = 22) ∧
    (∀ u ∈ cgraph.neighborSet w \ cgraph.commonNeighbors v w, cgraph.dist v u = 2) ∧
    (∀ u ∈ cgraph.neighborSet w, u ∈ cgraph.neighborSet v ∨ cgraph.dist v u = 2) ∧
    ∀ u, cgraph.Adj w u → cgraph.dist v u ≠ 3 :=
  type_three_neighborhood_global_distance_bound_of ambientRootOrbitsHyp hw

end CFSG.Monster.B.TwoA.Amalgam
