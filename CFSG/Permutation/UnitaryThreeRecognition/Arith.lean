module

public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.UnitaryThreeRecognition

theorem exponent_eq_of_count {p f s k : ℕ} (hp : 3 ≤ p) (hs : s < 3 * f)
    (heq : p ^ (3 * f) - p ^ s = (p ^ s + 1) * p ^ s * k) (hk : k ≤ 2 * (p ^ f - 1)) :
    s = f := by
  have hp1 : 1 < p := by omega
  have hA : 1 ≤ p ^ s := Nat.one_le_pow _ _ (by omega)
  have hAq : p ^ s ≤ p ^ (3 * f) := Nat.pow_le_pow_right (by omega) hs.le
  apply le_antisymm
  ·
    have hsplit : p ^ (3 * f) = p ^ s * p ^ (3 * f - s) := by
      rw [← pow_add]; congr 1; omega
    set A := p ^ s with hAdef
    set B := p ^ (3 * f - s) with hBdef
    have hB : p ≤ B := by
      rw [hBdef]
      calc p = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ (3 * f - s) := Nat.pow_le_pow_right (by omega) (by omega)
    have hBk : B - 1 = (A + 1) * k := by
      have h1 : A * (B - 1) = A * ((A + 1) * k) := by
        rw [Nat.mul_sub, mul_one, ← hsplit, heq]; ring
      exact Nat.eq_of_mul_eq_mul_left (by omega) h1
    have hk1 : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with h | h
      · rw [h, mul_zero] at hBk; omega
      · exact h
    have hBA : A < B := by
      have : (A + 1) * 1 ≤ (A + 1) * k := Nat.mul_le_mul_left _ hk1
      omega
    have h2s : s < 3 * f - s := by
      by_contra h
      push Not at h
      have : B ≤ A := Nat.pow_le_pow_right (by omega) h
      omega
    have hsplit2 : B = A * p ^ (3 * f - 2 * s) := by
      rw [hBdef, hAdef, ← pow_add]; congr 1; omega
    set C := p ^ (3 * f - 2 * s) with hCdef
    have hC : 1 ≤ C := Nat.one_le_pow _ _ (by omega)
    have hdvd : A + 1 ∣ C + 1 := by
      have h1 : A + 1 ∣ (A + 1) * C := dvd_mul_right _ _
      have h2 : A + 1 ∣ (A + 1) * C - (C + 1) := by
        have : (A + 1) * C - (C + 1) = B - 1 := by
          rw [hsplit2]
          have : (A + 1) * C = A * C + C := by ring
          omega
        rw [this, hBk]
        exact dvd_mul_right _ _
      have h3 : (A + 1) * C - ((A + 1) * C - (C + 1)) = C + 1 := by
        have : C + 1 ≤ (A + 1) * C := by nlinarith
        omega
      rw [← h3]
      exact Nat.dvd_sub h1 h2
    have hAC : A ≤ C := by
      have := Nat.le_of_dvd (by omega) hdvd
      omega
    have : s ≤ 3 * f - 2 * s := by
      by_contra h
      push Not at h
      have : C < A := Nat.pow_lt_pow_right (by omega) h
      omega
    omega
  ·
    by_contra h
    push Not at h
    set A := p ^ s with hAdef
    set q := p ^ f with hqdef
    have hpA : p * A ≤ q := by
      rw [hAdef, hqdef, ← pow_succ']
      exact Nat.pow_le_pow_right (by omega) h
    have h3A : 3 * A ≤ q := le_trans (Nat.mul_le_mul_right _ hp) hpA
    have hq3 : p ^ (3 * f) = q * q * q := by
      rw [hqdef, ← pow_two, ← pow_succ]; ring_nf
    have hq : 3 ≤ q := by omega
    have hkq : k ≤ 2 * q := by omega
    have hmain : q * q * q = (A + 1) * A * k + A := by
      have := heq
      rw [hq3] at this hAq
      omega
    have hbound : (A + 1) * A * k ≤ (A + 1) * A * (2 * q) := Nat.mul_le_mul_left _ hkq
    have h1 : q * q * q ≤ (A + 1) * A * (2 * q) + A := by linarith
    have h9 : 9 * (A * A) ≤ q * q := by nlinarith
    have h2 : 9 * ((A + 1) * A * (2 * q)) ≤ 2 * (q * q * q) + 6 * (q * q) := by
      have e : 9 * ((A + 1) * A * (2 * q)) = (2 * q) * (9 * (A * A)) + (6 * q) * (3 * A) := by
        ring
      rw [e]
      have := Nat.mul_le_mul_left (2 * q) h9
      have := Nat.mul_le_mul_left (6 * q) h3A
      nlinarith
    have h3 : 9 * A ≤ 3 * q := by omega
    have hqq : 3 * q ≤ q * q := Nat.mul_le_mul_right _ hq
    have hqqq : 3 * (q * q) ≤ q * q * q := by
      have := Nat.mul_le_mul_right (q * q) hq
      linarith [mul_comm q (q * q), mul_assoc q q q]
    nlinarith

end CFSG.UnitaryThreeRecognition
