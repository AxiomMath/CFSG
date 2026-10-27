module

public import CFSG.OddTranspositions.AalphaCommute

public section

namespace CFSG.OddTranspositions.QZ

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge
open CFSG.Timmesfeld.Bridge.Asc72

variable {G : Type} [Group G] [Finite G]

@[expose] def W (D : Set G) (u : G) (X : Subgroup G) (R : Subgroup X) [R.Normal]
    (huX : u ∈ X) : Set X :=
  {y : X | (y : G) ∈ D ∧ Commute (y : G) u ∧
    QuotientGroup.mk' R y ≠ QuotientGroup.mk' R ⟨u, huX⟩}

variable {D : Set G}

theorem mem_W_iff {u : G} {X : Subgroup G} {R : Subgroup X} [R.Normal] {huX : u ∈ X}
    {y : X} :
    y ∈ W D u X R huX ↔
      (y : G) ∈ D ∧ Commute (y : G) u ∧
        QuotientGroup.mk' R y ≠ QuotientGroup.mk' R ⟨u, huX⟩ :=
  Iff.rfl

theorem W_subset_D {u : G} {X : Subgroup G} {R : Subgroup X} [R.Normal] {huX : u ∈ X}
    (y : X) (hy : y ∈ W D u X R huX) : (y : G) ∈ D :=
  (mem_W_iff.mp hy).1

theorem W_commute_u {u : G} {X : Subgroup G} {R : Subgroup X} [R.Normal] {huX : u ∈ X}
    (y : X) (hy : y ∈ W D u X R huX) : Commute (y : G) u :=
  (mem_W_iff.mp hy).2.1

theorem C_D_u_subset_alpha_union (hC : HypothesisC D) {u : G} (hu : u ∈ hC.alpha)
    {x : G} (hx : x ∈ D) (hxu : Commute x u) :
    x ∈ hC.alpha ∪ DalphaStar D hC.alpha := by
  have hx' : x ∈ hC.alpha ∪ DalphaStar D hC.alpha ∪ AalphaStar D hC.alpha := by
    rw [← hC.eq_alpha_union]
    exact hx
  rcases hx' with (hxα | hxS) | hxA
  · exact Or.inl hxα
  · exact Or.inr hxS
  · exact absurd hxu (not_commute_of_mem_AalphaStar hC hxA hu)

theorem W_subset_alpha_union (hC : HypothesisC D) {u : G} (hu : u ∈ hC.alpha)
    {X : Subgroup G} {R : Subgroup X} [R.Normal] {huX : u ∈ X}
    (y : X) (hy : y ∈ W D u X R huX) :
    (y : G) ∈ hC.alpha ∪ DalphaStar D hC.alpha :=
  C_D_u_subset_alpha_union hC hu (W_subset_D y hy) (W_commute_u y hy)

end CFSG.OddTranspositions.QZ

end
