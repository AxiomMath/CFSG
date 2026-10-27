module

public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.Quasithin.H13.NQCore.U3O

theorem false_of_dvd_of_modEq {r m : ℕ} (hr : 3 ≤ r) (hm : 2 ≤ m)
    (hdvd : m ∣ (r - 1) * (r + 1) ^ 2) (hmod : r ^ 2 ∣ m - 1) : False := by
  obtain ⟨y, hy⟩ := hdvd
  obtain ⟨t, ht⟩ := hmod
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 3 := ⟨r - 3, by omega⟩
  have hm' : m = (k + 3) ^ 2 * t + 1 := by omega
  have ht1 : 1 ≤ t := by
    rcases Nat.eq_zero_or_pos t with h0 | h0
    · rw [h0] at hm'
      omega
    · exact h0
  have h1 : (k + 2) * (k + 4) ^ 2 = ((k + 3) ^ 2 * t + 1) * y := by
    have h2 : k + 3 - 1 = k + 2 := by omega
    rw [h2, hm'] at hy
    exact hy
  have hNy : (k + 3) ^ 3 + (k + 3) ^ 2 = (k + 3) + 1 + ((k + 3) ^ 2 * (t * y) + y) := by
    nlinarith [h1]
  have hypos : 1 ≤ y := by
    rcases Nat.eq_zero_or_pos y with h0 | h0
    · rw [h0] at h1
      simp at h1
    · exact h0
  have hyle : y ≤ k + 3 := by
    by_contra hlt
    push Not at hlt
    have h3 : (k + 3) ^ 2 * (t * y) ≥ (k + 3) ^ 2 * y := by
      apply Nat.mul_le_mul_left
      exact Nat.le_mul_of_pos_left y ht1
    nlinarith
  have hdvdZ : ((k + 3 : ℕ) : ℤ) ^ 2 ∣ ((k + 3 : ℕ) : ℤ) + 1 + y := by
    refine ⟨((k + 3 : ℕ) : ℤ) + 1 - (t * y : ℕ), ?_⟩
    have := congrArg (fun n : ℕ => (n : ℤ)) hNy
    push_cast at this ⊢
    linarith
  have hle := Int.le_of_dvd (by positivity) hdvdZ
  push_cast at hle
  nlinarith

theorem dvd_of_dvd_two_pow {r j : ℕ} (hr : 3 ≤ r) (hodd : r % 2 = 1)
    (hdvd : 2 ^ j ∣ r ^ 3 * ((r ^ 2 - 1) * (r ^ 3 + 1))) : 2 ^ j ∣ (r - 1) * (r + 1) ^ 2 := by
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
  have e1 : (k + 1) ^ 2 - 1 = k * (k + 2) := by
    have : (k + 1) ^ 2 = k * (k + 2) + 1 := by ring
    omega
  have h : (k + 1) ^ 3 * (((k + 1) ^ 2 - 1) * ((k + 1) ^ 3 + 1)) =
      ((k + 1 - 1) * (k + 1 + 1) ^ 2) * ((k + 1) ^ 3 * (k ^ 2 + k + 1)) := by
    rw [e1, Nat.add_sub_cancel]
    ring
  rw [h] at hdvd
  have hc : Nat.Coprime (2 ^ j) ((k + 1) ^ 3 * (k ^ 2 + k + 1)) := by
    refine Nat.Coprime.pow_left j (Nat.coprime_two_left.2 ?_)
    refine Odd.mul (Odd.pow (by rw [Nat.odd_iff]; omega)) ?_
    rw [Nat.odd_iff]
    have : k ^ 2 + k = k * (k + 1) := by ring
    have h2 : 2 ∣ k * (k + 1) := (Nat.even_mul_succ_self k).two_dvd
    omega
  exact hc.dvd_of_dvd_mul_right hdvd

end CFSG.Quasithin.H13.NQCore.U3O
