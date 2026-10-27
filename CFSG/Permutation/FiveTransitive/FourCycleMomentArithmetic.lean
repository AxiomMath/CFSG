module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG

namespace FiveTransitive.FourCycleMomentArithmetic

open scoped BigOperators

private theorem six_pattern_orbits
    {I : Type*} [Fintype I] (c4 c2 : I → ℕ) (N m : ℕ)
    (hshape : ∀ i, c4 i ≠ 0 → c2 i = 2 ∨ c2 i = 4)
    (htwo : ∃ i, 0 < c4 i ∧ c2 i = 2)
    (hfour : ∃ i, 0 < c4 i ∧ c2 i = 4)
    (h4 : ∑ i, c4 i = N) (h6 : ∑ i, c4 i * c2 i = N * m) :
    m = 3 := by
  have hlo : ∀ i, 2 * c4 i ≤ c4 i * c2 i := by
    intro i
    by_cases hi : c4 i = 0
    · simp [hi]
    · rcases hshape i hi with h | h <;> rw [h] <;> omega
  have hhi : ∀ i, c4 i * c2 i ≤ 4 * c4 i := by
    intro i
    by_cases hi : c4 i = 0
    · simp [hi]
    · rcases hshape i hi with h | h <;> rw [h] <;> omega
  have hltlo : (∑ i, 2 * c4 i) < ∑ i, c4 i * c2 i := by
    apply Finset.sum_lt_sum (fun i _ => hlo i)
    obtain ⟨i, hi, heq⟩ := hfour
    exact ⟨i, Finset.mem_univ i, by rw [heq]; omega⟩
  have hlthi : (∑ i, c4 i * c2 i) < ∑ i, 4 * c4 i := by
    apply Finset.sum_lt_sum (fun i _ => hhi i)
    obtain ⟨i, hi, heq⟩ := htwo
    exact ⟨i, Finset.mem_univ i, by rw [heq]; omega⟩
  rw [← Finset.mul_sum, h4, h6] at hltlo hlthi
  have hN : 0 < N := by nlinarith
  have hmlo : 2 < m := by nlinarith
  have hmhi : m < 4 := by nlinarith
  omega

private theorem eight_pattern_sum
    {I : Type*} [Fintype I] (c4 c2 : I → ℕ) (N : ℕ)
    (hshape : ∀ i, c4 i ≠ 0 → c2 i = 2 ∨ c2 i = 4)
    (h4 : ∑ i, c4 i = N) (h6 : ∑ i, c4 i * c2 i = N * 3) :
    ∑ i, c4 i * c2 i * (c2 i - 2) = N * 4 := by
  have heq : ∀ i, c4 i * c2 i * (c2 i - 2) + 8 * c4 i =
      4 * (c4 i * c2 i) := by
    intro i
    by_cases hi : c4 i = 0
    · simp [hi]
    · rcases hshape i hi with h | h <;> rw [h] <;> omega
  have hsum := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun i _ => heq i)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, h4, h6] at hsum
  omega

theorem six_and_eight_pattern_orbits
    {I : Type*} [Fintype I] (c4 c2 : I → ℕ) (N m6 m8 : ℕ) (hN : 0 < N)
    (hshape : ∀ i, c4 i ≠ 0 → c2 i = 2 ∨ c2 i = 4)
    (htwo : ∃ i, 0 < c4 i ∧ c2 i = 2)
    (hfour : ∃ i, 0 < c4 i ∧ c2 i = 4)
    (h4 : ∑ i, c4 i = N) (h6 : ∑ i, c4 i * c2 i = N * m6)
    (h8 : ∑ i, c4 i * c2 i * (c2 i - 2) = N * m8) :
    m6 = 3 ∧ m8 = 4 := by
  have hthree := six_pattern_orbits c4 c2 N m6 hshape htwo hfour h4 h6
  refine ⟨hthree, ?_⟩
  have hsum := eight_pattern_sum c4 c2 N hshape h4 (by simpa only [hthree] using h6)
  rw [h8] at hsum
  exact Nat.eq_of_mul_eq_mul_left hN hsum

end FiveTransitive.FourCycleMomentArithmetic

end CFSG
