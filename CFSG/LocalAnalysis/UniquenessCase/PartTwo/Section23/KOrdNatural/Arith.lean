module

public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Tactic.Finiteness.Attr
public import Mathlib.Tactic.ToDual
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KOrdNat

private lemma sq_add_one_mul_sq_sub_one (q : ℕ) :
    (q ^ 2 + 1) * (q ^ 2 - 1) = q ^ 4 - 1 := by
  rw [← Nat.sq_sub_sq (q ^ 2) 1, show q ^ 4 = (q ^ 2) ^ 2 by ring]

private lemma sq_sub_one_pos {q : ℕ} (hq : 2 ≤ q) : 0 < q ^ 2 - 1 := by
  have h2 : 2 ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left hq 2
  norm_num at h2
  omega

theorem ordL2_ne_ordOmegaMinusFour {q : ℕ} (hq : 2 ≤ q) :
    q * (q ^ 2 - 1) ≠ q ^ 2 * (q ^ 4 - 1) := by
  intro h
  have hpos := sq_sub_one_pos hq
  rw [← sq_add_one_mul_sq_sub_one q] at h
  rw [show q ^ 2 * ((q ^ 2 + 1) * (q ^ 2 - 1))
        = (q ^ 2 * (q ^ 2 + 1)) * (q ^ 2 - 1) by ring] at h
  have hq2 : q = q ^ 2 * (q ^ 2 + 1) := Nat.mul_right_cancel hpos h
  nlinarith [hq]

theorem not_sq_dvd_ordL2 {q : ℕ} (hq : 2 ≤ q) : ¬ q ^ 2 ∣ q * (q ^ 2 - 1) := by
  intro h
  have hq0 : 0 < q := by omega
  have hqsq : 1 ≤ q ^ 2 := by nlinarith [hq]
  have h' : q * q ∣ q * (q ^ 2 - 1) := by
    simpa [show q ^ 2 = q * q by ring] using h
  have hdiv : q ∣ q ^ 2 - 1 := Nat.dvd_of_mul_dvd_mul_left hq0 h'
  have hq2 : q ∣ q ^ 2 := ⟨q, by ring⟩
  have hone : q ∣ 1 := by
    have hsub := Nat.dvd_sub hq2 hdiv
    rwa [show q ^ 2 - (q ^ 2 - 1) = 1 by omega] at hsub
  have hle := Nat.le_of_dvd (by norm_num : 0 < 1) hone
  omega

theorem not_pow_three_dvd_ordL2 {q : ℕ} (hq : 2 ≤ q) : ¬ q ^ 3 ∣ q * (q ^ 2 - 1) := by
  intro h
  exact not_sq_dvd_ordL2 hq (dvd_trans ⟨q, by ring⟩ h)

theorem not_pow_three_dvd_ordOmegaMinusFour {q : ℕ} (hq : 2 ≤ q) :
    ¬ q ^ 3 ∣ q ^ 2 * (q ^ 4 - 1) := by
  intro h
  have hq0 : 0 < q := by omega
  have hqsq : 1 ≤ q ^ 2 := by nlinarith [hq]
  have hq4le : 1 ≤ q ^ 4 := by nlinarith [hq]
  have h' : q ^ 2 * q ∣ q ^ 2 * (q ^ 4 - 1) := by
    simpa [show q ^ 3 = q ^ 2 * q by ring] using h
  have hdiv : q ∣ q ^ 4 - 1 := Nat.dvd_of_mul_dvd_mul_left (pow_pos hq0 2) h'
  have hq4 : q ∣ q ^ 4 := ⟨q ^ 3, by ring⟩
  have hone : q ∣ 1 := by
    have hsub := Nat.dvd_sub hq4 hdiv
    rwa [show q ^ 4 - (q ^ 4 - 1) = 1 by omega] at hsub
  have hle := Nat.le_of_dvd (by norm_num : 0 < 1) hone
  omega

theorem not_ordOmegaMinusFour_dvd_ordOFourPlus {q : ℕ} (hq : 2 ≤ q) :
    ¬ q ^ 2 * (q ^ 4 - 1) ∣ 2 * q ^ 2 * (q ^ 2 - 1) ^ 2 := by
  intro h
  have hq0 : 0 < q := by omega
  have hqsq : 1 ≤ q ^ 2 := by nlinarith [hq]
  have h' : q ^ 2 * (q ^ 4 - 1) ∣ q ^ 2 * (2 * (q ^ 2 - 1) ^ 2) := by
    convert h using 1 <;> ring
  have hdiv : q ^ 4 - 1 ∣ 2 * (q ^ 2 - 1) ^ 2 :=
    Nat.dvd_of_mul_dvd_mul_left (pow_pos hq0 2) h'
  rw [← sq_add_one_mul_sq_sub_one q] at hdiv
  have hpos := sq_sub_one_pos hq
  have h'2 : (q ^ 2 - 1) * (q ^ 2 + 1) ∣ (q ^ 2 - 1) * (2 * (q ^ 2 - 1)) := by
    convert hdiv using 1 <;> ring
  have hdiv2 : q ^ 2 + 1 ∣ 2 * (q ^ 2 - 1) :=
    Nat.dvd_of_mul_dvd_mul_left hpos h'2
  have hdvd4 : q ^ 2 + 1 ∣ 4 := by
    have h1 : q ^ 2 + 1 ∣ 2 * (q ^ 2 + 1) := ⟨2, by ring⟩
    have hsub := Nat.dvd_sub h1 hdiv2
    have h4 : 2 * (q ^ 2 + 1) - 2 * (q ^ 2 - 1) = 4 := by omega
    rwa [h4] at hsub
  have hle := Nat.le_of_dvd (by norm_num : 0 < 4) hdvd4
  have h5 : 5 ≤ q ^ 2 + 1 := by nlinarith [hq]
  omega

end CFSG.LocalAnalysis.UniquenessCase.UC22.KOrdNat

end
