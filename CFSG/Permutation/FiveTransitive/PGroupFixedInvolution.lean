module

public import Mathlib.Data.Rat.Floor
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG

namespace FiveTransitive.PGroupFixedInvolution

open MulAction

theorem exists_involution
    {G X : Type*} [Group G] [Finite G] [Finite X] [MulAction G X]
    (Q : Subgroup G) (hQ : IsPGroup 2 Q) (hne : Q ≠ ⊥) :
    ∃ t : G, t ∈ Q ∧ orderOf t = 2 ∧
      fixedPoints Q X ⊆ fixedBy X t ∧
      Nat.card (fixedPoints Q X) ≤ (fixedBy X t).ncard := by
  classical
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : Nontrivial Q := Q.nontrivial_iff_ne_bot.mpr hne
  obtain ⟨q, hq⟩ := exists_ne (1 : Q)
  let u : Q := q ^ (orderOf q / 2)
  have hu : orderOf u = 2 :=
    orderOf_pow_orderOf_div (ne_of_gt (orderOf_pos q)) (hQ.dvd_orderOf hq)
  have hsub : fixedPoints Q X ⊆ fixedBy X (u : G) := by
    intro x hx
    exact mem_fixedPoints.mp hx u
  refine ⟨u, u.property, (Subgroup.orderOf_coe u).trans hu, hsub, ?_⟩
  rw [Nat.card_coe_set_eq]
  exact Set.ncard_le_ncard hsub

end FiveTransitive.PGroupFixedInvolution

end CFSG
