module

public import CFSG.Monster.B.TwoA.Amalgam.RankFiveMatrix
public import CFSG.Monster.B.TwoA.Amalgam.GlobalTypeFinal

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA

theorem native_type_four_neighborhood_global_distance_bound_uncond
    {v w : CVert}
    (hw : w ∈ sphereFour v) {Ω : Fin 8 → Set CVert}
    (hsub : ∀ i, Ω i ⊆ cgraph.neighborSet v) (hpart : ∀ u ∈ cgraph.neighborSet v, ∃! i, u ∈ Ω i)
    (horb : ∀ i, ∀ u ∈ Ω i, cvOrbit (vStab v ⊓ vStab w) u = Ω i)
    (hcard : ∀ i, (Ω i).ncard = ![648, 8064, 663552, 1, 1134, 36288, 1161216, 2097152] i) :
    (∀ u ∈ cgraph.neighborSet v, u ∉ Ω 1 → cgraph.dist w u ≤ 2) ∧
    (cgraph.neighborSet v ∩ sphereDistThree w = ∅ ∨
      cgraph.neighborSet v ∩ sphereDistThree w = Ω 1) ∧
    (∀ x ∈ Ω 1, ∀ y ∈ Ω 0, ¬ cgraph.Adj x y) ∧
    (∀ y ∈ Ω 5, (cgraph.neighborSet y ∩ Ω 0).ncard = 24) ∧
    (∀ M : RootModel v, M.LabelCompat → ∀ x y : cgraph.neighborSet v,
      (orderOf (M.pt x * M.pt y) = 3 ↔ LabelThree x y)) ∧
    (∀ y ∈ Ω 7, {x | x ∈ Ω 0 ∧ LabelThree x y}.ncard = 324) ∧
    (∀ y ∈ Ω 6, ∃ x ∈ Ω 0, LabelThree x y) :=
  native_type_four_neighborhood_global_distance_bound fischer_remaining_orbit_global_types.2
    (GSide.hno_of_ambient ambientRootOrbitsHyp) hw hsub hpart horb hcard

theorem native_rank_five_exact_neighbor_matrix :
    (∀ v w : CVert, ∃! i, w ∈ (![{v}, cgraph.neighborSet v, sphereThree v, sphereFour v,
      sphereDistThree v] : Fin 5 → Set CVert) i) ∧
    (∀ (v : CVert) (i : Fin 5), ∀ w ∈ (![{v}, cgraph.neighborSet v, sphereThree v, sphereFour v,
      sphereDistThree v] : Fin 5 → Set CVert) i,
      vStabOrbit v w = (![{v}, cgraph.neighborSet v, sphereThree v, sphereFour v,
        sphereDistThree v] : Fin 5 → Set CVert) i) ∧
    ∀ (v : CVert) (i j : Fin 5), ∀ w ∈ (![{v}, cgraph.neighborSet v, sphereThree v, sphereFour v,
      sphereDistThree v] : Fin 5 → Set CVert) i,
      (cgraph.neighborSet w ∩ (![{v}, cgraph.neighborSet v, sphereThree v, sphereFour v,
        sphereDistThree v] : Fin 5 → Set CVert) j).ncard =
        (!![0, 3968055, 0, 0, 0; 1, 46134, 2097152, 1824768, 0; 0, 3510, 837135, 3127410, 0;
          0, 648, 663552, 3295791, 8064; 0, 0, 0, 3898440, 69615] : Matrix (Fin 5) (Fin 5) ℕ)
          i j :=
  native_rank_five_exact_neighbor_matrix_of_ambient ambientRootOrbitsHyp

end CFSG.Monster.B.TwoA.Amalgam
