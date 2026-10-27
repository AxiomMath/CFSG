module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.Quasithin.C116Two

theorem four_pow_gt (j : ℕ) (hj : 1 ≤ j) : j + 1 < 4 ^ j := by
  induction j with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · norm_num
    · have := ih hn
      calc n + 1 + 1 < 4 ^ n + 1 := by omega
        _ ≤ 4 ^ n * 4 := by have : 1 ≤ 4 ^ n := Nat.one_le_pow _ _ (by norm_num); omega
        _ = 4 ^ (n + 1) := by ring

theorem orbit_arith {a c z u y b f k : ℕ} (hz : 0 < z) (hc : 0 < c) (hu : 0 < u) (hk : 0 < k)
    (h1 : a * z ^ k = c * u ^ k) (h2 : a ≤ k * b * f) (h3 : f * z ≤ c * y) (h4 : b * y ≤ u)
    (h5 : 4 * z ≤ u) : k = 1 := by
  by_contra hne
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hj : 1 ≤ j := by omega
  have e1 : c * u ^ (j + 1) * z ≤ c * ((j + 1) * u * z ^ (j + 1)) := by
    calc c * u ^ (j + 1) * z = (a * z ^ (j + 1)) * z := by rw [← h1]
      _ ≤ ((j + 1) * b * f) * z ^ (j + 1) * z := by
          exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h2)
      _ = (j + 1) * b * (f * z) * z ^ (j + 1) := by ring
      _ ≤ (j + 1) * b * (c * y) * z ^ (j + 1) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h3)
      _ = c * ((j + 1) * (b * y) * z ^ (j + 1)) := by ring
      _ ≤ c * ((j + 1) * u * z ^ (j + 1)) := by
          apply Nat.mul_le_mul_left
          exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h4)
  have e2 : u ^ (j + 1) * z ≤ (j + 1) * u * z ^ (j + 1) := by
    have e1' : c * (u ^ (j + 1) * z) ≤ c * ((j + 1) * u * z ^ (j + 1)) := by
      calc c * (u ^ (j + 1) * z) = c * u ^ (j + 1) * z := by ring
        _ ≤ _ := e1
    exact Nat.le_of_mul_le_mul_left e1' hc
  have e3 : u ^ j ≤ (j + 1) * z ^ j := by
    have : u * u ^ j * z ≤ (j + 1) * u * (z * z ^ j) := by
      calc u * u ^ j * z = u ^ (j + 1) * z := by ring
        _ ≤ (j + 1) * u * z ^ (j + 1) := e2
        _ = (j + 1) * u * (z * z ^ j) := by ring
    have h6 : (u * z) * u ^ j ≤ (u * z) * ((j + 1) * z ^ j) := by
      calc (u * z) * u ^ j = u * u ^ j * z := by ring
        _ ≤ (j + 1) * u * (z * z ^ j) := this
        _ = (u * z) * ((j + 1) * z ^ j) := by ring
    exact Nat.le_of_mul_le_mul_left h6 (Nat.mul_pos hu hz)
  have e4 : (4 * z) ^ j ≤ u ^ j := Nat.pow_le_pow_left h5 j
  have e5 : 4 ^ j * z ^ j ≤ (j + 1) * z ^ j := by
    calc 4 ^ j * z ^ j = (4 * z) ^ j := by rw [mul_pow]
      _ ≤ u ^ j := e4
      _ ≤ (j + 1) * z ^ j := e3
  have e6 : 4 ^ j ≤ j + 1 := Nat.le_of_mul_le_mul_right e5 (Nat.pow_pos hz)
  have := four_pow_gt j hj
  omega

end CFSG.Quasithin.C116Two
