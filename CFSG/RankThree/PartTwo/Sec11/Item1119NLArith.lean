module

public import Mathlib.Data.Nat.Notation
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.Int.Star
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
import Mathlib.Tactic.Monotonicity.Lemmas
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Presheaf

public section

namespace CFSG.RankThree.PartTwo.Sec11.Item1119NL

theorem two_pow_le_of_dvd_pred_mul_succ {k u : ℕ} (hk : 1 ≤ k) (hu : 4 ≤ u)
    (h : 2 ^ k ∣ (u - 1) * u * (u + 1)) : 2 ^ k ≤ 2 * (u + 1) := by
  obtain ⟨t, ht | ht⟩ := Nat.even_or_odd' u
  ·
    subst ht
    have e : (2 * t - 1) * (2 * t) * (2 * t + 1) = 2 * t * ((2 * t - 1) * (2 * t + 1)) := by
      ring
    rw [e] at h
    have h1 : Nat.Coprime 2 (2 * t - 1) := Nat.prime_two.coprime_iff_not_dvd.mpr (by omega)
    have h2 : Nat.Coprime 2 (2 * t + 1) := Nat.prime_two.coprime_iff_not_dvd.mpr (by omega)
    have hcop : Nat.Coprime (2 ^ k) ((2 * t - 1) * (2 * t + 1)) :=
      Nat.Coprime.mul_right (Nat.Coprime.pow_left k h1) (Nat.Coprime.pow_left k h2)
    have hdvd : 2 ^ k ∣ 2 * t := Nat.Coprime.dvd_of_dvd_mul_right hcop h
    have hle : 2 ^ k ≤ 2 * t := Nat.le_of_dvd (by omega) hdvd
    omega
  ·
    subst ht
    have e1 : 2 * t + 1 - 1 = 2 * t := by omega
    rw [e1] at h
    have e : 2 * t * (2 * t + 1) * (2 * t + 1 + 1) = 4 * (t * (t + 1)) * (2 * t + 1) := by
      ring
    rw [e] at h
    have hu' : Nat.Coprime (2 ^ k) (2 * t + 1) :=
      Nat.Coprime.pow_left k (Nat.prime_two.coprime_iff_not_dvd.mpr (by omega))
    have h4 : 2 ^ k ∣ 4 * (t * (t + 1)) := Nat.Coprime.dvd_of_dvd_mul_right hu' h
    rcases Nat.lt_or_ge k 3 with hk3 | hk3
    · have hk4 : 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hk5 : 2 ^ k ≤ 4 := hk4.trans (by norm_num)
      omega
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
      have e2 : 2 ^ (j + 2) = 4 * 2 ^ j := by ring
      rw [e2] at h4 ⊢
      have h6 : 2 ^ j ∣ t * (t + 1) :=
        (mul_dvd_mul_iff_left (by norm_num : (4 : ℕ) ≠ 0)).mp h4
      have hj : 2 ^ j ≤ t + 1 := by
        rcases Nat.mod_two_eq_zero_or_one t with htm | htm
        ·
          have hc : Nat.Coprime (2 ^ j) (t + 1) :=
            Nat.Coprime.pow_left j (Nat.prime_two.coprime_iff_not_dvd.mpr (by omega))
          have h8 : 2 ^ j ∣ t := Nat.Coprime.dvd_of_dvd_mul_right hc h6
          have h9 : 2 ^ j ≤ t := Nat.le_of_dvd (by omega) h8
          omega
        ·
          have hc : Nat.Coprime (2 ^ j) t :=
            Nat.Coprime.pow_left j (Nat.prime_two.coprime_iff_not_dvd.mpr (by omega))
          have h8 : 2 ^ j ∣ t + 1 := Nat.Coprime.dvd_of_dvd_mul_left hc h6
          exact Nat.le_of_dvd (by omega) h8
      omega

private theorem cube_ge_512_int {X : ℤ} (hX : 8 ≤ X) : (512 : ℤ) ≤ X ^ 3 := by
  have hX0 : 0 ≤ X := by linarith
  have h8 : 0 ≤ X - 8 := by linarith
  nlinarith [mul_nonneg (mul_nonneg h8 hX0) hX0, mul_nonneg h8 hX0]

private theorem poly_lt_case1_int {X : ℤ} (hX : 8 ≤ X) :
    8 * ((X ^ 2 - 1) * (X ^ 3 + 1)) < (X ^ 3 - 4) * (X ^ 3 - 2) := by
  have hX0 : 0 ≤ X := by linarith
  have h5 : 0 ≤ X ^ 5 * (X - 8) := mul_nonneg (pow_nonneg hX0 5) (by linarith)
  have h2 : 0 ≤ X ^ 2 * (X - 4) := mul_nonneg (pow_nonneg hX0 2) (by linarith)
  nlinarith

private theorem poly_lt_case2_int {X : ℤ} (hX : 8 ≤ X) :
    2 * ((X ^ 2 - 1) * (X ^ 3 + 1)) < (X ^ 3 - 2) * (X ^ 3 - 1) := by
  have hX0 : 0 ≤ X := by linarith
  have hC := cube_ge_512_int hX
  have h5 : 0 ≤ X ^ 5 * (X - 8) := mul_nonneg (pow_nonneg hX0 5) (by linarith)
  have h3 : 0 ≤ X ^ 3 * (X ^ 2 - 1) := mul_nonneg (pow_nonneg hX0 3) (by nlinarith)
  have h2 : 0 ≤ X ^ 2 * (X ^ 3 - 2) := mul_nonneg (pow_nonneg hX0 2) (by linarith)
  nlinarith [pow_nonneg hX0 5]

private theorem mul3_mono_int {a b c x y z : ℤ} (ha : a ≤ x) (hb : b ≤ y) (hc : c ≤ z)
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (hc0 : 0 ≤ c) :
    a * b * c ≤ x * y * z := by
  have h1 : a * b ≤ x * y := mul_le_mul ha hb hb0 (le_trans ha0 ha)
  exact mul_le_mul h1 hc hc0 (le_trans (mul_nonneg ha0 hb0) h1)

private theorem case1_int {X U M : ℤ} (hX : 8 ≤ X) (hle : X ^ 3 ≤ 2 * (U + 1))
    (hMe : M = (U - 1) * U * (U + 1))
    (hM : M ≤ X ^ 3 * ((X ^ 2 - 1) * (X ^ 3 + 1))) : False := by
  have hC := cube_ge_512_int hX
  have H1 : (X ^ 3 - 4) * (X ^ 3 - 2) * X ^ 3 ≤ (2 * U - 2) * (2 * U) * (2 * U + 2) :=
    mul3_mono_int (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
      (by linarith)
  have H2 : 8 * ((X ^ 2 - 1) * (X ^ 3 + 1)) * X ^ 3
      < (X ^ 3 - 4) * (X ^ 3 - 2) * X ^ 3 :=
    mul_lt_mul_of_pos_right (poly_lt_case1_int hX) (by linarith)
  linarith

private theorem case2_int {X U M : ℤ} (hX : 8 ≤ X) (hle : X ^ 3 ≤ U + 1)
    (hMe : 2 * M = (U - 1) * U * (U + 1))
    (hM : M ≤ X ^ 3 * ((X ^ 2 - 1) * (X ^ 3 + 1))) : False := by
  have hC := cube_ge_512_int hX
  have H1 : (X ^ 3 - 2) * (X ^ 3 - 1) * X ^ 3 ≤ (U - 1) * U * (U + 1) :=
    mul3_mono_int (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
      (by linarith)
  have H2 : 2 * ((X ^ 2 - 1) * (X ^ 3 + 1)) * X ^ 3
      < (X ^ 3 - 2) * (X ^ 3 - 1) * X ^ 3 :=
    mul_lt_mul_of_pos_right (poly_lt_case2_int hX) (by linarith)
  linarith

theorem false_of_sl2_order
    (hP : ∀ k u : ℕ, 1 ≤ k → 4 ≤ u → 2 ^ k ∣ (u - 1) * u * (u + 1) → 2 ^ k ≤ 2 * (u + 1))
    {n u T M : ℕ} (hn : 3 ≤ n) (hu : 4 ≤ u) (hT : T = 1 ∨ T = 2)
    (hM : M = (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 + 1)) ∨
          M = (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)))
    (h : T * M = u * (u ^ 2 - 1)) : False := by
  obtain ⟨q, hq⟩ : ∃ q, q = 2 ^ n := ⟨_, rfl⟩
  have hq8 : 8 ≤ q := by
    rw [hq]
    calc (8 : ℕ) = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hq3 : 2 ^ (3 * n) = q ^ 3 := by rw [hq]; ring
  have hq3' : 2 ^ (3 * n + 1) = 2 * q ^ 3 := by rw [hq]; ring
  rw [← hq] at hM
  have hu1 : 1 ≤ u := by omega
  have hq1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have ha : u * (u ^ 2 - 1) = (u - 1) * u * (u + 1) := by
    obtain ⟨v, rfl⟩ : ∃ v, u = v + 1 := ⟨u - 1, by omega⟩
    have h1 : (v + 1) ^ 2 - 1 = v * (v + 2) := by
      have h2 : (v + 1) ^ 2 = v * (v + 2) + 1 := by ring
      rw [h2, Nat.add_sub_cancel]
    rw [h1, Nat.add_sub_cancel]
    ring
  rw [ha] at h
  have hMdvd : q ^ 3 ∣ M := by
    rcases hM with hM | hM <;> rw [hM] <;> exact dvd_mul_right _ _
  have hMle : M ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) := by
    rcases hM with hM | hM
    · exact le_of_eq hM
    · rw [hM]
      exact Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (by omega))
  have hq8z : (8 : ℤ) ≤ (q : ℤ) := by exact_mod_cast hq8
  rcases hT with rfl | rfl
  · rw [one_mul] at h
    have hdvd : 2 ^ (3 * n) ∣ (u - 1) * u * (u + 1) := by
      rw [← h, hq3]
      exact hMdvd
    have hle := hP (3 * n) u (by omega) hu hdvd
    rw [hq3] at hle
    zify [hu1, hq1] at h hMle hle
    exact case1_int hq8z hle h hMle
  · have hdvd : 2 ^ (3 * n + 1) ∣ (u - 1) * u * (u + 1) := by
      rw [← h, hq3']
      exact mul_dvd_mul_left 2 hMdvd
    have hle := hP (3 * n + 1) u (by omega) hu hdvd
    rw [hq3'] at hle
    zify [hu1, hq1] at h hMle hle
    exact case2_int hq8z (by linarith) h hMle

end CFSG.RankThree.PartTwo.Sec11.Item1119NL

end
