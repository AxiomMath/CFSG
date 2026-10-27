
module

public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourActionData
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79.KL34

open CFSG.ComponentClassification.PSL3Four

theorem mem_closure_pair_pow {G : Type*} [Group G] {a b : G} (hab : a * b = b * a)
    (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) {x : G} (hx : x ∈ Subgroup.closure {a, b}) :
    ∃ i j : ℕ, x = a ^ i * b ^ j := by
  have hc : Commute a b := hab
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact ⟨1, 0, by simp⟩
    · exact ⟨0, 1, by simp⟩
  | one => exact ⟨0, 0, by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨i, j, rfl⟩ := hx
    obtain ⟨i', j', rfl⟩ := hy
    refine ⟨i + i', j + j', ?_⟩
    have : b ^ j * a ^ i' = a ^ i' * b ^ j := ((hc.symm.pow_pow j i')).eq
    calc a ^ i * b ^ j * (a ^ i' * b ^ j') = a ^ i * (b ^ j * a ^ i') * b ^ j' := by group
      _ = a ^ i * (a ^ i' * b ^ j) * b ^ j' := by rw [this]
      _ = a ^ (i + i') * b ^ (j + j') := by rw [pow_add, pow_add]; group
  | inv x _ hx =>
    obtain ⟨i, j, rfl⟩ := hx
    refine ⟨2 * i, 2 * j, ?_⟩
    have h1 : a ^ i * a ^ (2 * i) = 1 := by
      rw [← pow_add, show i + 2 * i = 3 * i by ring, pow_mul, ha, one_pow]
    have h2 : b ^ j * b ^ (2 * j) = 1 := by
      rw [← pow_add, show j + 2 * j = 3 * j by ring, pow_mul, hb, one_pow]
    have hcom : b ^ j * a ^ (2 * i) = a ^ (2 * i) * b ^ j := ((hc.symm.pow_pow j (2 * i))).eq
    rw [inv_eq_iff_mul_eq_one]
    calc a ^ i * b ^ j * (a ^ (2 * i) * b ^ (2 * j))
        = a ^ i * (b ^ j * a ^ (2 * i)) * b ^ (2 * j) := by group
      _ = a ^ i * (a ^ (2 * i) * b ^ j) * b ^ (2 * j) := by rw [hcom]
      _ = (a ^ i * a ^ (2 * i)) * (b ^ j * b ^ (2 * j)) := by group
      _ = 1 := by rw [h1, h2, one_mul]

theorem pow_eq_pow_mod_three {G : Type*} [Group G] {a : G} (ha : a ^ 3 = 1) (i : ℕ) :
    a ^ i = a ^ (i % 3) := by
  conv_lhs => rw [← Nat.mod_add_div i 3, pow_add, pow_mul, ha, one_pow, mul_one]

end CFSG.RankThree.PartTwo.Sec21.FF79.KL34
