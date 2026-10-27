module

public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.Quasithin.Z7a

theorem mul_pred_mul_le_of_div_le (d e : ℕ) {B : ℕ} (h : d * (d - 1) * e / 2 ≤ B) :
    d * (d - 1) * e ≤ 2 * B := by
  obtain ⟨k, hk⟩ := Nat.even_mul_pred_self d
  rw [hk] at h ⊢
  have h1 : (k + k) * e = 2 * (k * e) := by ring
  rw [h1] at h ⊢
  omega

theorem mul_pred_mul_eq (d e : ℕ) : d * (d - 1) * e = (d - 1) * (d * e) := by ring

theorem numeric_L2 {d e n : ℕ} (hn : 2 ≤ n) (hd : 3 ≤ d) (hde : 2 * n ≤ d * e)
    (hKI : d * (d - 1) * e ≤ 4 * n + 2) : d = 3 ∧ 3 * e < 2 * n + 2 := by
  rw [mul_pred_mul_eq] at hKI
  have hd1 : 2 ≤ d - 1 := by omega
  have h1 : (d - 1) * (2 * n) ≤ (d - 1) * (d * e) := Nat.mul_le_mul_left _ hde
  have hd3 : d = 3 := by
    by_contra hne
    have hd4 : 3 ≤ d - 1 := by omega
    have h2 : 3 * (2 * n) ≤ (d - 1) * (2 * n) := Nat.mul_le_mul_right _ hd4
    omega
  subst hd3
  refine ⟨rfl, ?_⟩
  have : 2 * (3 * e) ≤ 4 * n + 2 := by
    have h3 : (3 - 1) * (3 * e) = 2 * (3 * e) := by norm_num
    omega
  omega

theorem numeric_Sz {d e n : ℕ} (hn : 3 ≤ n) (hd : 3 ≤ d) (hde : 4 * n ≤ d * e)
    (hKI : d * (d - 1) * e ≤ 4 * (2 * n - 1) + 2) : False := by
  rw [mul_pred_mul_eq] at hKI
  have hd1 : 2 ≤ d - 1 := by omega
  have h1 : (d - 1) * (4 * n) ≤ (d - 1) * (d * e) := Nat.mul_le_mul_left _ hde
  have h2 : 2 * (4 * n) ≤ (d - 1) * (4 * n) := Nat.mul_le_mul_right _ hd1
  omega

theorem numeric_J1 {d e : ℕ} (hd : 3 ≤ d) (hde : 18 ≤ d * e)
    (hKI : d * (d - 1) * e ≤ 4 * 3 + 2) : False := by
  rw [mul_pred_mul_eq] at hKI
  have hd1 : 2 ≤ d - 1 := by omega
  have h1 : (d - 1) * 18 ≤ (d - 1) * (d * e) := Nat.mul_le_mul_left _ hde
  have h2 : 2 * 18 ≤ (d - 1) * 18 := Nat.mul_le_mul_right _ hd1
  omega

theorem numeric_Lp {d e : ℕ} (hd : 3 ≤ d) (he : 1 ≤ e) (hKI : d * (d - 1) * e ≤ 4 * 2 + 2) :
    d = 3 ∧ e = 1 := by
  have hd3 : d = 3 := by
    by_contra hne
    have hd4 : 4 ≤ d := by omega
    have h1 : 4 * 3 ≤ d * (d - 1) := Nat.mul_le_mul hd4 (by omega)
    have h2 : d * (d - 1) * 1 ≤ d * (d - 1) * e := Nat.mul_le_mul_left _ he
    omega
  subst hd3
  refine ⟨rfl, ?_⟩
  norm_num at hKI
  omega

theorem eq_seven_of_card_le {p : ℕ} (hp : 7 ≤ p) (h : p * (p ^ 2 - 1) ≤ 336) : p = 7 := by
  by_contra hne
  have hp8 : 8 ≤ p := by omega
  have h1 : 8 ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left hp8 2
  have h2 : 8 * 63 ≤ p * (p ^ 2 - 1) := Nat.mul_le_mul hp8 (by omega)
  omega

end CFSG.Quasithin.Z7a
