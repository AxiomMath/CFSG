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

private lemma ggQ2s08_lin_aux : ∀ k : ℕ, 6 * (k + 10) ≤ 3 ^ (k + 9) := by
  intro k
  induction k with
  | zero => norm_num
  | succ k ih =>
    have h1 : (k + 1) + 10 = (k + 10) + 1 := by omega
    have h2 : (k + 1) + 9 = (k + 9) + 1 := by omega
    rw [h1, h2, pow_succ]
    nlinarith [ih]

private lemma ggQ2s08_lin (m : ℕ) (hm : 9 ≤ m) : 6 * (m + 1) ≤ 3 ^ m := by
  have h := ggQ2s08_lin_aux (m - 9)
  have h1 : m - 9 + 10 = m + 1 := by omega
  have h2 : m - 9 + 9 = m := by omega
  rwa [h1, h2] at h

private lemma ggQ2s08_tri (m : ℕ) : m + m * (m - 1) / 2 = (m + 1) * m / 2 := by
  have h1 : m * (m - 1) / 2 = m.choose 2 := (Nat.choose_two_right m).symm
  have h2 : (m + 1) * m / 2 = (m + 1).choose 2 := by
    rw [Nat.choose_two_right (m + 1)]
    simp
  rw [h1, h2, Nat.choose_succ_succ m 1, Nat.choose_one_right m]

theorem ggQ2s08_count_irr {N : ℕ} (hN : 10 ≤ N) :
    8 * (3 ^ N * (4 * (2 ^ (N - 1) * (N - 1).factorial))) < 3 ^ (N * (N - 1) / 2) := by
  refine Nat.le_induction (m := 10)
    (P := fun N _ => 8 * (3 ^ N * (4 * (2 ^ (N - 1) * (N - 1).factorial))) <
      3 ^ (N * (N - 1) / 2)) ?base ?step N hN
  · norm_num [Nat.factorial]
  · intro m hm ih
    rw [show (m + 1) - 1 = m by omega]
    have hm1 : m - 1 + 1 = m := by omega
    have hfac : m.factorial = m * (m - 1).factorial := by
      have h := Nat.factorial_succ (m - 1)
      rwa [hm1] at h
    have h2m : 2 ^ m = 2 ^ (m - 1) * 2 := by
      have h := pow_succ 2 (m - 1)
      rwa [hm1] at h
    have hident : 8 * (3 ^ (m + 1) * (4 * (2 ^ m * m.factorial)))
        = 6 * m * (8 * (3 ^ m * (4 * (2 ^ (m - 1) * (m - 1).factorial)))) := by
      rw [pow_succ, hfac, h2m]
      ring
    have hbound : 6 * m ≤ 3 ^ m :=
      le_trans (Nat.mul_le_mul_left 6 (Nat.le_succ m)) (ggQ2s08_lin m (by omega))
    calc
      8 * (3 ^ (m + 1) * (4 * (2 ^ m * m.factorial)))
          = 6 * m * (8 * (3 ^ m * (4 * (2 ^ (m - 1) * (m - 1).factorial)))) := hident
      _ ≤ 3 ^ m * (8 * (3 ^ m * (4 * (2 ^ (m - 1) * (m - 1).factorial)))) :=
            Nat.mul_le_mul_right _ hbound
      _ < 3 ^ m * 3 ^ (m * (m - 1) / 2) :=
            mul_lt_mul_of_pos_left ih (pow_pos (by norm_num) m)
      _ = 3 ^ (m + m * (m - 1) / 2) := by rw [← pow_add]
      _ = 3 ^ ((m + 1) * m / 2) := by rw [ggQ2s08_tri m]

theorem ggQ2s08_count_red {r : ℕ} (hr : 9 ≤ r) :
    8 * (2 * 3 ^ r * (4 * (2 ^ r * r.factorial))) < 3 ^ (r * (r - 1) / 2) := by
  refine Nat.le_induction (m := 9)
    (P := fun r _ => 8 * (2 * 3 ^ r * (4 * (2 ^ r * r.factorial))) <
      3 ^ (r * (r - 1) / 2)) ?base ?step r hr
  · norm_num [Nat.factorial]
  · intro m hm ih
    rw [show (m + 1) - 1 = m by omega]
    have hident : 8 * (2 * 3 ^ (m + 1) * (4 * (2 ^ (m + 1) * (m + 1).factorial)))
        = 6 * (m + 1) * (8 * (2 * 3 ^ m * (4 * (2 ^ m * m.factorial)))) := by
      rw [pow_succ, Nat.factorial_succ]
      ring
    have hbound : 6 * (m + 1) ≤ 3 ^ m := ggQ2s08_lin m hm
    calc
      8 * (2 * 3 ^ (m + 1) * (4 * (2 ^ (m + 1) * (m + 1).factorial)))
          = 6 * (m + 1) * (8 * (2 * 3 ^ m * (4 * (2 ^ m * m.factorial)))) := hident
      _ ≤ 3 ^ m * (8 * (2 * 3 ^ m * (4 * (2 ^ m * m.factorial)))) :=
            Nat.mul_le_mul_right _ hbound
      _ < 3 ^ m * 3 ^ (m * (m - 1) / 2) :=
            mul_lt_mul_of_pos_left ih (pow_pos (by norm_num) m)
      _ = 3 ^ (m + m * (m - 1) / 2) := by rw [← pow_add]
      _ = 3 ^ ((m + 1) * m / 2) := by rw [ggQ2s08_tri m]

end CFSG.StandardType

end
