module

public import CFSG.Timmesfeld.Orders.ExceptionalWeylData
public import CFSG.Timmesfeld.Orders.ExceptionalTorus
public import CFSG.LieType.Chevalley.AdjointCenter

public noncomputable section

namespace CFSG.Timmesfeld.ExceptionalOrders

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open

theorem ncard_posRoots_G2 :
    {α : Fin Tag.G2.rank → ℤ | IsRoot .G2 α ∧ 0 < height α}.ncard = 6 :=
  (ncard_setOf_isRoot_and fun α => 0 < height α).trans (by decide +kernel)

theorem ncard_posRoots_F4 :
    {α : Fin Tag.F4.rank → ℤ | IsRoot .F4 α ∧ 0 < height α}.ncard = 24 :=
  (ncard_setOf_isRoot_and fun α => 0 < height α).trans (by decide +kernel)

theorem ncard_posRoots_E6 :
    {α : Fin Tag.E6.rank → ℤ | IsRoot .E6 α ∧ 0 < height α}.ncard = 36 :=
  (ncard_setOf_isRoot_and fun α => 0 < height α).trans (by decide +kernel)

theorem ncard_posRoots_E7 :
    {α : Fin Tag.E7.rank → ℤ | IsRoot .E7 α ∧ 0 < height α}.ncard = 63 :=
  (ncard_setOf_isRoot_and fun α => 0 < height α).trans (by decide +kernel)

theorem ncard_posRoots_E8 :
    {α : Fin Tag.E8.rank → ℤ | IsRoot .E8 α ∧ 0 < height α}.ncard = 120 :=
  (ncard_setOf_isRoot_and fun α => 0 < height α).trans (by decide +kernel)

section Formulas

variable (q : ℕ) (hq : 1 ≤ q)
include hq

theorem ordG2_eq : (q - 1) ^ 2 * q ^ 6 * (geomSum 2 1 q * geomSum 6 1 q) = ordG2 q := by
  have h : ∀ n, 1 ≤ q ^ n := fun n => Nat.one_le_pow _ _ hq
  unfold ordG2 geomSum
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  zify [hq, h 6, h 2]
  ring

theorem ordF4_eq : (q - 1) ^ 4 * q ^ 24 * (geomSum 2 1 q * geomSum 3 1 q *
    (geomSum 4 1 q * geomSum 2 3 q) * (geomSum 8 1 q * geomSum 3 4 q)) = ordF4 q := by
  have h : ∀ n, 1 ≤ q ^ n := fun n => Nat.one_le_pow _ _ hq
  unfold ordF4 geomSum
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  zify [hq, h 12, h 8, h 6, h 2]
  ring

theorem ordE6_mul : (q - 1) ^ 6 * q ^ 36 * (geomSum 2 1 q * geomSum 3 1 q * geomSum 4 1 q *
    geomSum 5 1 q * (geomSum 2 3 q * geomSum 8 1 q) * (geomSum 9 1 q * geomSum 3 4 q)) =
      q ^ 36 * (q ^ 12 - 1) * (q ^ 9 - 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 - 1) *
        (q ^ 2 - 1) := by
  have h : ∀ n, 1 ≤ q ^ n := fun n => Nat.one_le_pow _ _ hq
  unfold geomSum
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  zify [hq, h 12, h 9, h 8, h 6, h 5, h 2]
  ring

theorem ordE7_mul : (q - 1) ^ 7 * q ^ 63 * (geomSum 2 1 q * geomSum 3 1 q * geomSum 4 1 q *
    geomSum 5 1 q * (geomSum 2 3 q * geomSum 8 1 q) * (geomSum 9 1 q * geomSum 3 4 q) *
      (geomSum 2 5 q * geomSum 2 9 q * geomSum 14 1 q)) =
      q ^ 63 * (q ^ 18 - 1) * (q ^ 14 - 1) * (q ^ 12 - 1) * (q ^ 10 - 1) * (q ^ 8 - 1) *
        (q ^ 6 - 1) * (q ^ 2 - 1) := by
  have h : ∀ n, 1 ≤ q ^ n := fun n => Nat.one_le_pow _ _ hq
  unfold geomSum
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  zify [hq, h 18, h 14, h 12, h 10, h 8, h 6, h 2]
  ring

theorem ordE8_eq : (q - 1) ^ 8 * q ^ 120 * (geomSum 2 1 q * geomSum 3 1 q * geomSum 4 1 q *
    geomSum 5 1 q * (geomSum 2 3 q * geomSum 8 1 q) * (geomSum 9 1 q * geomSum 3 4 q) *
      (geomSum 2 5 q * geomSum 2 9 q * geomSum 14 1 q) *
        (geomSum 24 1 q * geomSum 2 10 q * geomSum 5 6 q)) = ordE8 q := by
  have h : ∀ n, 1 ≤ q ^ n := fun n => Nat.one_le_pow _ _ hq
  unfold ordE8 geomSum
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  zify [hq, h 30, h 24, h 20, h 18, h 14, h 12, h 8, h 2]
  ring

end Formulas

section Orders

variable {K : Type} [Field K] [Finite K]

theorem one_le_card_field : 1 ≤ Nat.card K :=
  Nat.card_pos

theorem card_adjointGroup_G2 : Nat.card (adjointGroup .G2 K) = ordG2 (Nat.card K) := by
  classical
  have : Fintype (WeylGroup .G2) := Fintype.ofFinite _
  rw [card_adjointGroup, finsum_eq_sum_of_fintype, sum_length_G2, card_torusGroup_G2,
    ncard_posRoots_G2, ← ordG2_eq _ one_le_card_field]

theorem card_adjointGroup_F4 : Nat.card (adjointGroup .F4 K) = ordF4 (Nat.card K) := by
  classical
  have : Fintype (WeylGroup .F4) := Fintype.ofFinite _
  rw [card_adjointGroup, finsum_eq_sum_of_fintype, sum_length_F4, card_torusGroup_F4,
    ncard_posRoots_F4, ← ordF4_eq _ one_le_card_field]

theorem card_adjointGroup_E8 : Nat.card (adjointGroup .E8 K) = ordE8 (Nat.card K) := by
  classical
  have : Fintype (WeylGroup .E8) := Fintype.ofFinite _
  rw [card_adjointGroup, finsum_eq_sum_of_fintype, sum_length_E8, card_torusGroup_E8,
    ncard_posRoots_E8, ← ordE8_eq _ one_le_card_field]

theorem card_adjointGroup_E6 : Nat.card (adjointGroup .E6 K) = ordE6 (Nat.card K) := by
  classical
  have : Fintype (WeylGroup .E6) := Fintype.ofFinite _
  have hH := card_torusGroup_E6 (K := K)
  rw [card_adjointGroup, finsum_eq_sum_of_fintype, sum_length_E6, ncard_posRoots_E6, ordE6,
    ← ordE6_mul _ one_le_card_field, ← hH, Nat.gcd_comm]
  refine (Nat.div_eq_of_eq_mul_left (Nat.gcd_pos_of_pos_left _ (by norm_num)) ?_).symm
  ring

theorem card_adjointGroup_E7 : Nat.card (adjointGroup .E7 K) = ordE7 (Nat.card K) := by
  classical
  have : Fintype (WeylGroup .E7) := Fintype.ofFinite _
  have hH := card_torusGroup_E7 (K := K)
  rw [card_adjointGroup, finsum_eq_sum_of_fintype, sum_length_E7, ncard_posRoots_E7, ordE7,
    ← ordE7_mul _ one_le_card_field, ← hH, Nat.gcd_comm]
  refine (Nat.div_eq_of_eq_mul_left (Nat.gcd_pos_of_pos_left _ (by norm_num)) ?_).symm
  ring

theorem card_adjointQuotient (τ : Tag) :
    Nat.card (AdjointQuotient τ K) = Nat.card (adjointGroup τ K) := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (Subgroup.center (adjointGroup τ K))
  rw [(Subgroup.card_eq_one).2 center_adjointGroup_eq_bot, mul_one] at h
  exact h.symm

end Orders

section Models

variable {G : Type} [Group G] {q : ℕ}

theorem card_of_untwistedChevalleyModel {τ : Tag} (h : UntwistedChevalleyModel G τ q) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = q ∧
      Nat.card G = Nat.card (adjointGroup τ K) := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h
  exact ⟨K, inferInstance, inferInstance, hK, (Nat.card_congr e.toEquiv).trans
    (card_adjointQuotient τ)⟩

theorem card_of_untwistedChevalleyModel_G2 (h : UntwistedChevalleyModel G .G2 q) :
    Nat.card G = ordG2 q := by
  obtain ⟨K, _, _, rfl, hG⟩ := card_of_untwistedChevalleyModel h
  rw [hG, card_adjointGroup_G2]

theorem card_of_untwistedChevalleyModel_F4 (h : UntwistedChevalleyModel G .F4 q) :
    Nat.card G = ordF4 q := by
  obtain ⟨K, _, _, rfl, hG⟩ := card_of_untwistedChevalleyModel h
  rw [hG, card_adjointGroup_F4]

theorem card_of_untwistedChevalleyModel_E6 (h : UntwistedChevalleyModel G .E6 q) :
    Nat.card G = ordE6 q := by
  obtain ⟨K, _, _, rfl, hG⟩ := card_of_untwistedChevalleyModel h
  rw [hG, card_adjointGroup_E6]

theorem card_of_untwistedChevalleyModel_E7 (h : UntwistedChevalleyModel G .E7 q) :
    Nat.card G = ordE7 q := by
  obtain ⟨K, _, _, rfl, hG⟩ := card_of_untwistedChevalleyModel h
  rw [hG, card_adjointGroup_E7]

theorem card_of_untwistedChevalleyModel_E8 (h : UntwistedChevalleyModel G .E8 q) :
    Nat.card G = ordE8 q := by
  obtain ⟨K, _, _, rfl, hG⟩ := card_of_untwistedChevalleyModel h
  rw [hG, card_adjointGroup_E8]

end Models

end CFSG.Timmesfeld.ExceptionalOrders
