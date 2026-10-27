module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155L143Abs
public import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.Perm.Cycle.Concrete

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155L143

open Equiv Equiv.Perm

section Perm

variable {α : Type*} [Fintype α] [DecidableEq α]

private theorem exists_cycleType_eq_replicate_three {σ : Perm α} (h : σ ^ 3 = 1) :
    ∃ k : ℕ, σ.cycleType = Multiset.replicate k 3 ∧ σ.support.card = 3 * k := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine ⟨σ.cycleType.card, cycleType_of_pow_prime_eq_one h, ?_⟩
  have hsum := sum_cycleType σ
  rw [cycleType_of_pow_prime_eq_one h, Multiset.sum_replicate, smul_eq_mul] at hsum
  omega

private theorem isConj_of_pow_three_of_card_support_eq {σ τ : Perm α} (hσ : σ ^ 3 = 1)
    (hτ : τ ^ 3 = 1) (h : σ.support.card = τ.support.card) : IsConj σ τ := by
  obtain ⟨k, hk, hk'⟩ := exists_cycleType_eq_replicate_three hσ
  obtain ⟨l, hl, hl'⟩ := exists_cycleType_eq_replicate_three hτ
  rw [isConj_iff_cycleType_eq, hk, hl, show k = l by omega]

private theorem card_support_eq_three_or_six {σ : Perm α} (hα : Fintype.card α < 9)
    (h3 : σ ^ 3 = 1) (h1 : σ ≠ 1) : σ.support.card = 3 ∨ σ.support.card = 6 := by
  obtain ⟨k, -, hk⟩ := exists_cycleType_eq_replicate_three h3
  have hle : σ.support.card ≤ Fintype.card α := Finset.card_le_univ _
  have hne : σ.support.card ≠ 0 := fun h0 => h1 (card_support_eq_zero.mp h0)
  omega

end Perm

theorem L143Row.of_isConj_alternating {α : Type*} [Fintype α] [DecidableEq α]
    {x r : alternatingGroup α} (h : IsConj (x : Perm α) (r : Perm α)) (hr : L143Row r) :
    L143Row x := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  refine L143Row.of_mulEquiv (MulAut.conjNormal c : MulAut (alternatingGroup α)) ?_
  have hx : (MulAut.conjNormal c : MulAut (alternatingGroup α)) x = r :=
    Subtype.ext (by rw [MulAut.conjNormal_apply]; exact hc)
  rwa [hx]

private theorem eq_one_or_eq_or_eq_sq_of_mem_zpowers {G : Type*} [Group G] {x y : G}
    (hx : x ^ 3 = 1) (hy : y ∈ Subgroup.zpowers x) : y = 1 ∨ y = x ∨ y = x ^ 2 := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  rw [zpow_eq_zpow_emod' k hx]
  have hk : k % ((3 : ℕ) : ℤ) = 0 ∨ k % ((3 : ℕ) : ℤ) = 1 ∨ k % ((3 : ℕ) : ℤ) = 2 := by omega
  rcases hk with h | h | h <;> rw [h] <;> simp

private theorem l143Row_alternating_of_data {α : Type*} [Fintype α] [DecidableEq α]
    {x y s : Perm α} (h : sign x = 1 ∧ x ^ 3 = 1 ∧ sign y = 1 ∧ sign s = 1 ∧ y * x = x * y ∧
      y ^ 3 = 1 ∧ y ≠ 1 ∧ y ≠ x ∧ y ≠ x ^ 2 ∧ s * y * s⁻¹ = y⁻¹) :
    L143Row (⟨x, mem_alternatingGroup.mpr h.1⟩ : alternatingGroup α) := by
  obtain ⟨hx, hx3, hy, hs, hyx, hy3, hy1, hyx1, hyx2, hsy⟩ := h
  refine Or.inl ⟨⟨y, mem_alternatingGroup.mpr hy⟩, ⟨s, mem_alternatingGroup.mpr hs⟩,
    Subtype.ext hyx, Subtype.ext hy3, ?_, Subtype.ext hsy⟩
  intro hmem
  rcases eq_one_or_eq_or_eq_sq_of_mem_zpowers (Subtype.ext hx3) hmem with h | h | h
  · exact hy1 (congrArg Subtype.val h)
  · exact hyx1 (congrArg Subtype.val h)
  · exact hyx2 (congrArg Subtype.val h)

private theorem l143Rows_alternating_of_data {α : Type*} [Fintype α] [DecidableEq α]
    (hα : Fintype.card α < 9) (x₁ y₁ s₁ x₂ y₂ s₂ : Perm α)
    (h₁ : x₁.support.card = 3 ∧ sign x₁ = 1 ∧ x₁ ^ 3 = 1 ∧ sign y₁ = 1 ∧ sign s₁ = 1 ∧
      y₁ * x₁ = x₁ * y₁ ∧ y₁ ^ 3 = 1 ∧ y₁ ≠ 1 ∧ y₁ ≠ x₁ ∧ y₁ ≠ x₁ ^ 2 ∧ s₁ * y₁ * s₁⁻¹ = y₁⁻¹)
    (h₂ : x₂.support.card = 6 ∧ sign x₂ = 1 ∧ x₂ ^ 3 = 1 ∧ sign y₂ = 1 ∧ sign s₂ = 1 ∧
      y₂ * x₂ = x₂ * y₂ ∧ y₂ ^ 3 = 1 ∧ y₂ ≠ 1 ∧ y₂ ≠ x₂ ∧ y₂ ≠ x₂ ^ 2 ∧ s₂ * y₂ * s₂⁻¹ = y₂⁻¹) :
    L143Rows (alternatingGroup α) := by
  intro x hx3 hx1
  have hx3' : (x : Perm α) ^ 3 = 1 := congrArg Subtype.val hx3
  have hx1' : (x : Perm α) ≠ 1 := fun h => hx1 (Subtype.ext h)
  rcases card_support_eq_three_or_six hα hx3' hx1' with h | h
  · exact L143Row.of_isConj_alternating (r := ⟨x₁, mem_alternatingGroup.mpr h₁.2.1⟩)
      (isConj_of_pow_three_of_card_support_eq hx3' h₁.2.2.1 (h.trans h₁.1.symm))
      (l143Row_alternating_of_data h₁.2)
  · exact L143Row.of_isConj_alternating (r := ⟨x₂, mem_alternatingGroup.mpr h₂.2.1⟩)
      (isConj_of_pow_three_of_card_support_eq hx3' h₂.2.2.1 (h.trans h₂.1.symm))
      (l143Row_alternating_of_data h₂.2)

theorem l143Rows_alternating_six : L143Rows (alternatingGroup (Fin 6)) :=
  l143Rows_alternating_of_data (by simp) c[0, 1, 2] c[3, 4, 5] (swap 3 4 * swap 0 1)
    (c[0, 1, 2] * c[3, 4, 5]) c[0, 1, 2] (swap 0 1 * swap 3 4) (by decide) (by decide)

theorem l143Rows_alternating_seven : L143Rows (alternatingGroup (Fin 7)) :=
  l143Rows_alternating_of_data (by simp) c[0, 1, 2] c[3, 4, 5] (swap 3 4 * swap 0 1)
    (c[0, 1, 2] * c[3, 4, 5]) c[0, 1, 2] (swap 0 1 * swap 3 4) (by decide) (by decide)

end CFSG.RankThree.PartTwo.Sec15.Sylow155L143
