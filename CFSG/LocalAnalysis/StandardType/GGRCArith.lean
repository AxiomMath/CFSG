module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Measurability.Init
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt

public section

namespace CFSG.StandardType

private lemma l05nK3b_lin_aux : ∀ k : ℕ, 2 * (k + 10) ≤ 3 ^ (k + 8) := by
  intro k
  induction k with
  | zero => norm_num
  | succ k ih =>
    have h1 : (k + 1) + 10 = (k + 10) + 1 := by omega
    have h2 : (k + 1) + 8 = (k + 8) + 1 := by omega
    rw [h1, h2, pow_succ]
    nlinarith [ih]

private lemma l05nK3b_lin (m : ℕ) (hm : 9 ≤ m) : 2 * (m + 1) ≤ 3 ^ (m - 1) := by
  have h := l05nK3b_lin_aux (m - 9)
  have h1 : m - 9 + 10 = m + 1 := by omega
  have h2 : m - 9 + 8 = m - 1 := by omega
  rwa [h1, h2] at h

private lemma l05nK3b_tri (m : ℕ) : m + m * (m - 1) / 2 = (m + 1) * m / 2 := by
  have h1 : m * (m - 1) / 2 = m.choose 2 := (Nat.choose_two_right m).symm
  have h2 : (m + 1) * m / 2 = (m + 1).choose 2 := by
    rw [Nat.choose_two_right (m + 1)]
    simp
  rw [h1, h2, Nat.choose_succ_succ m 1, Nat.choose_one_right m]

private lemma l05nK3b_nine {p W : ℕ} (hp3 : 3 ≤ p) (hW : 8 * (6 * W) < 3 ^ 26) :
    8 * (p ^ 9 * ((p - 1) * 6 * W)) < p ^ 36 := by
  have hp0 : 0 < p := by omega
  have hmid : (p - 1) * (8 * (6 * W)) < p * 3 ^ 26 := by
    have h1 : (p - 1) * (8 * (6 * W)) ≤ (p - 1) * 3 ^ 26 :=
      Nat.mul_le_mul_left _ (le_of_lt hW)
    have h2 : (p - 1) * 3 ^ 26 < p * 3 ^ 26 :=
      Nat.mul_lt_mul_of_pos_right (by omega : p - 1 < p) (by norm_num : 0 < 3 ^ 26)
    exact lt_of_le_of_lt h1 h2
  calc
    8 * (p ^ 9 * ((p - 1) * 6 * W))
        = p ^ 9 * ((p - 1) * (8 * (6 * W))) := by ring
    _ < p ^ 9 * (p * 3 ^ 26) := mul_lt_mul_of_pos_left hmid (pow_pos hp0 9)
    _ ≤ p ^ 9 * p ^ 27 := by
          apply Nat.mul_le_mul_left
          calc
            p * 3 ^ 26 ≤ p * p ^ 26 := Nat.mul_le_mul_left p (Nat.pow_le_pow_left hp3 26)
            _ = p ^ 27 := by ring
    _ = p ^ 36 := by ring

private lemma l05nK3b_key {p n : ℕ} (hp3 : 3 ≤ p) (hn : 9 ≤ n) :
    8 * (p ^ n * ((p - 1) * 6 * (2 ^ n * n.factorial))) < p ^ (n * (n - 1) / 2) := by
  have hp0 : 0 < p := by omega
  refine Nat.le_induction (m := 9)
    (P := fun n _ => 8 * (p ^ n * ((p - 1) * 6 * (2 ^ n * n.factorial))) <
      p ^ (n * (n - 1) / 2)) ?base ?step n hn
  · have hb : 8 * (6 * (2 ^ 9 * Nat.factorial 9)) < 3 ^ 26 := by norm_num
    have h9 : 9 * (9 - 1) / 2 = 36 := by norm_num
    rw [h9]
    exact l05nK3b_nine hp3 hb
  · intro m hm ih
    have hident : 8 * (p ^ (m + 1) * ((p - 1) * 6 * (2 ^ (m + 1) * (m + 1).factorial)))
        = p * (2 * (m + 1)) * (8 * (p ^ m * ((p - 1) * 6 * (2 ^ m * m.factorial)))) := by
      rw [pow_succ, Nat.factorial_succ]
      ring
    have hbound : p * (2 * (m + 1)) ≤ p ^ m := by
      have hlin : 2 * (m + 1) ≤ p ^ (m - 1) :=
        le_trans (l05nK3b_lin m hm) (Nat.pow_le_pow_left hp3 (m - 1))
      calc
        p * (2 * (m + 1)) ≤ p * p ^ (m - 1) := Nat.mul_le_mul_left p hlin
        _ = p ^ m := by
              rw [mul_comm, ← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ m)]
    calc
      8 * (p ^ (m + 1) * ((p - 1) * 6 * (2 ^ (m + 1) * (m + 1).factorial)))
          = p * (2 * (m + 1)) * (8 * (p ^ m * ((p - 1) * 6 * (2 ^ m * m.factorial)))) :=
            hident
      _ ≤ p ^ m * (8 * (p ^ m * ((p - 1) * 6 * (2 ^ m * m.factorial)))) :=
            Nat.mul_le_mul_right _ hbound
      _ < p ^ m * p ^ (m * (m - 1) / 2) := mul_lt_mul_of_pos_left ih (pow_pos hp0 m)
      _ = p ^ (m + m * (m - 1) / 2) := by rw [← pow_add]
      _ = p ^ ((m + 1) * m / 2) := by rw [l05nK3b_tri m]

theorem ggRC_arith {p n W : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : 9 ≤ n)
    (hW : W ≤ 2 ^ n * n.factorial ∨ (n = 9 ∧ W = 696729600)) :
    8 * (p ^ n * ((p - 1) * 6 * W)) < p ^ (n * (n - 1) / 2) := by
  have hp3 : 3 ≤ p := by
    have h2 := hp.two_le
    omega
  rcases hW with hW | ⟨rfl, rfl⟩
  · have hsmall : (p - 1) * 6 * W ≤ (p - 1) * 6 * (2 ^ n * n.factorial) :=
      Nat.mul_le_mul_left _ hW
    have hmono : 8 * (p ^ n * ((p - 1) * 6 * W)) ≤
        8 * (p ^ n * ((p - 1) * 6 * (2 ^ n * n.factorial))) :=
      Nat.mul_le_mul_left 8 (Nat.mul_le_mul_left _ hsmall)
    exact lt_of_le_of_lt hmono (l05nK3b_key hp3 hn)
  · have h9 : 9 * (9 - 1) / 2 = 36 := by norm_num
    rw [h9]
    exact l05nK3b_nine hp3 (by norm_num)

end CFSG.StandardType
