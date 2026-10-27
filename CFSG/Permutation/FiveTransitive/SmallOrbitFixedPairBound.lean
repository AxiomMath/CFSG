module

public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.GroupTheory.GroupAction.FixedPoints
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG

namespace FiveTransitive.SmallOrbitFixedPairBound

open MulAction

theorem sum_fixed_eq_sum_stabilizers
    {G X : Type*} [Group G] [Fintype G] [Fintype X] [MulAction G X] :
    (∑ g : G, Nat.card (fixedBy X g)) = ∑ x : X, Nat.card (stabilizer G x) := by
  classical
  simp only [Nat.card_eq_fintype_card]
  change (∑ g : G, Fintype.card {x : X // g • x = x}) =
    ∑ x : X, Fintype.card {g : G // g • x = x}
  simp only [Fintype.card_subtype,Finset.card_eq_sum_ones,Finset.sum_filter]
  exact Finset.sum_comm

theorem card_le_four
    {G X : Type*} [Group G] [Finite G] [Fintype X] [MulAction G X]
    (hX : Fintype.card X = 36)
    (s : Finset X) (hs : s.card = 15) (hfixed : ∀ g : G, ∀ x ∈ s, g • x = x)
    (horbit : ∀ x : X, Nat.card (orbit G x) ≤ 3)
    (hbound : ∀ g : G, g ≠ 1 → Nat.card (fixedBy X g) ≤ 18) : Nat.card G ≤ 4 := by
  classical
  let _ : Fintype G := Fintype.ofFinite G
  have hpoint : ∀ x : X,
      Nat.card G + (if x ∈ s then 2 * Nat.card G else 0) ≤ 3 * Nat.card (stabilizer G x) := by
    intro x
    by_cases hx : x ∈ s
    · have he : stabilizer G x = ⊤ := by
        apply le_antisymm le_top
        intro g _
        exact hfixed g x hx
      simp only [hx,ite_true,he,Subgroup.card_top]
      omega
    · simp only [hx,ite_false,add_zero]
      have he := card_orbit_mul_card_stabilizer_eq_card_group G x
      simp only [← Nat.card_eq_fintype_card] at he
      have hl := Nat.mul_le_mul_right (Nat.card (stabilizer G x)) (horbit x)
      rwa [he] at hl
  have hsum := Finset.sum_le_sum (fun x (_ : x ∈ (Finset.univ : Finset X)) => hpoint x)
  have hlow : 66 * Nat.card G ≤ 3 * ∑ x : X, Nat.card (stabilizer G x) := by
    rw [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,hX,
      ← Finset.mul_sum] at hsum
    have he : (∑ x : X, if x ∈ s then 2 * Nat.card G else 0) = 15 * (2 * Nat.card G) := by
      rw [← Finset.sum_filter]
      simp [hs]
    rw [he] at hsum
    omega
  rw [← sum_fixed_eq_sum_stabilizers] at hlow
  have hupper : (∑ g : G, Nat.card (fixedBy X g)) ≤
      (Nat.card G - 1) * 18 + 36 := by
    have hone : Nat.card (fixedBy X (1 : G)) = 36 := by
      rw [fixedBy_one_eq_univ,Nat.card_coe_set_eq,Set.ncard_univ,Nat.card_eq_fintype_card,hX]
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (1 : G)),hone]
    have hb := Finset.sum_le_sum (fun g (hg : g ∈ (Finset.univ : Finset G).erase 1) =>
      hbound g (Finset.mem_erase.mp hg).1)
    have hbc : (∑ g ∈ (Finset.univ : Finset G).erase 1, Nat.card (fixedBy X g)) ≤
        (Nat.card G - 1) * 18 := by
      simpa only [Finset.sum_const,nsmul_eq_mul,Finset.card_erase_of_mem (Finset.mem_univ (1 : G)),
        Finset.card_univ,← Nat.card_eq_fintype_card,Nat.cast_id] using hb
    exact Nat.add_le_add_right hbc _
  omega

end FiveTransitive.SmallOrbitFixedPairBound

end CFSG
