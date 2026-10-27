module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.Int.Star
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.Walter.WardLocal

theorem bound_aux {q a d : ℤ} (hq : 3 ≤ q) (hd : 3 ≤ d) (ha : Even a) (hda : d ∣ a - 1)
    (h : 1 - a * q + a ^ 2 * q ^ 2 ≤ q ^ 2 * d) : False := by
  have ha1 : a ≠ 1 := by rintro rfl; exact (Int.not_even_one) ha
  have ha0 : a ≠ 0 := by
    rintro rfl
    have := Int.le_of_dvd one_pos (by simpa using (dvd_neg.mpr hda))
    omega
  have hb : d ≤ |a - 1| := Int.le_of_dvd (abs_pos.mpr (sub_ne_zero.mpr ha1)) ((dvd_abs _ _).mpr hda)
  have hab : |a - 1| ≤ |a| + 1 := by
    calc |a - 1| ≤ |a| + |(1 : ℤ)| := abs_sub _ _
      _ = |a| + 1 := by simp
  have h2 : 2 ≤ |a| := by
    obtain ⟨r, hr⟩ := ha
    rcases abs_cases a with ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega
  have hsq : a ^ 2 = |a| ^ 2 := (sq_abs a).symm
  have hneg : -a * q ≥ -(|a| * q) := by
    have := le_abs_self a
    nlinarith
  rcases (show |a| = 2 ∨ 3 ≤ |a| by omega) with hA | hA
  · have hd3 : d = 3 := by omega
    rcases abs_cases a with ⟨h1, _⟩ | ⟨h1, _⟩
    · have : a = 2 := by omega
      subst this
      rw [hd3] at hda
      norm_num at hda
    · have : a = -2 := by omega
      subst this hd3
      nlinarith
  · have hdb : d ≤ |a| + 1 := by omega
    rw [hsq] at h
    set b := |a| with hbdef
    have k1 : q ^ 2 * d ≤ q ^ 2 * (b + 1) := by
      have : 0 ≤ q ^ 2 := sq_nonneg q
      nlinarith
    have k2 : b ^ 2 - b - 1 ≥ b + 2 := by nlinarith
    have k3 : q ^ 2 * (b ^ 2 - b - 1) ≥ q ^ 2 * (b + 2) := by
      have : 0 ≤ q ^ 2 := sq_nonneg q
      nlinarith
    have k4 : q ^ 2 * (b + 2) > b * q := by
      have h5 : q * (b + 2) - b > 0 := by nlinarith
      have h6 := mul_pos (show (0 : ℤ) < q by omega) h5
      nlinarith
    nlinarith

theorem three_not_dvd_aux {q : ℤ} (hq : 3 ∣ q) : ¬ (3 : ℤ) ∣ (q - 1) * (q ^ 2 + 1) := by
  obtain ⟨r, rfl⟩ := hq
  obtain ⟨X, hX⟩ : ∃ X : ℤ, (3 * r - 1) * ((3 * r) ^ 2 + 1) = 3 * X - 1 :=
    ⟨r + 9 * r ^ 3 - 3 * r ^ 2, by ring⟩
  rw [hX]
  omega

theorem isCoprime_three_pow_sub_one {n : ℕ} (hn : 1 ≤ n) (t : ℕ) :
    IsCoprime ((3 : ℤ) ^ t) ((3 : ℤ) ^ n - 1) := by
  apply IsCoprime.pow_left
  refine ⟨3 ^ (n - 1), -1, ?_⟩
  have : (3 : ℤ) ^ n = 3 * 3 ^ (n - 1) := by
    rw [← pow_succ']; congr 1; omega
  rw [this]; ring

theorem cT_arith {n j : ℕ} {q a N : ℤ} (hq : q = 3 ^ n) (hn : 1 ≤ n) (hj : j ≤ 3 * n)
    (ha : Even a) (hN : N * (2 * 3 ^ j) ^ 2 = q ^ 4 * (q - 1) * ((a * (q + 1) - 1) ^ 2 + q ^ 2))
    (hlow : 1 + (1 - a * q) ^ 2 + (a * q) ^ 2 ≤ 2 * 3 ^ j) :
    a = 0 ∧ j ≤ 2 * n := by
  have hq3 : 3 ≤ q := by
    rw [hq]; calc (3 : ℤ) = 3 ^ 1 := by norm_num
      _ ≤ 3 ^ n := pow_le_pow_right₀ (by norm_num) hn
  have hq4 : q ^ 4 = 3 ^ (4 * n) := by rw [hq, ← pow_mul, mul_comm]
  by_cases ha0 : a = 0
  · refine ⟨ha0, ?_⟩
    by_contra hlt
    push Not at hlt
    obtain ⟨t, ht⟩ : ∃ t, j = 2 * n + 1 + t := ⟨j - (2 * n + 1), by omega⟩
    subst ha0
    have hpow : (2 * (3 : ℤ) ^ j) ^ 2 = 3 ^ (4 * n) * (36 * 3 ^ (2 * t)) := by
      rw [ht, mul_pow, ← pow_mul, show (2 * n + 1 + t) * 2 = 4 * n + 2 + 2 * t by ring,
        pow_add, pow_add]
      ring
    rw [hpow, hq4] at hN
    have h1 : (3 : ℤ) ^ (4 * n) * (36 * N * 3 ^ (2 * t)) =
        (3 : ℤ) ^ (4 * n) * ((q - 1) * (q ^ 2 + 1)) := by
      linear_combination hN
    have h2 := mul_left_cancel₀ (pow_ne_zero _ (by norm_num : (3 : ℤ) ≠ 0)) h1
    exact three_not_dvd_aux (show (3 : ℤ) ∣ q by rw [hq]; exact dvd_pow_self 3 (by omega))
      ⟨12 * N * 3 ^ (2 * t), by linear_combination -h2⟩
  · exfalso
    have h2 : 2 ≤ |a| := by
      obtain ⟨r, hr⟩ := ha
      rcases abs_cases a with ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega
    have hgt : 2 * n < j := by
      by_contra hle
      push Not at hle
      have h3 : (3 : ℤ) ^ j ≤ q ^ 2 := by
        rw [hq, ← pow_mul]; exact pow_le_pow_right₀ (by norm_num) (by omega)
      have habs : a ^ 2 ≥ 4 := by nlinarith [sq_abs a]
      have : (1 - a * q) ^ 2 + (a * q) ^ 2 ≥ 4 * q ^ 2 := by nlinarith
      nlinarith
    obtain ⟨t, ht⟩ : ∃ t, j = 2 * n + t := ⟨j - 2 * n, by omega⟩
    have ht1 : 1 ≤ t := by omega
    have htn : t ≤ n := by omega
    set d : ℤ := 3 ^ t with hd
    have hd3 : 3 ≤ d := by
      rw [hd]; calc (3 : ℤ) = 3 ^ 1 := by norm_num
        _ ≤ 3 ^ t := pow_le_pow_right₀ (by norm_num) ht1
    have hdq : d ∣ q := by rw [hq, hd]; exact pow_dvd_pow 3 htn
    have h3j : (3 : ℤ) ^ j = q ^ 2 * d := by rw [ht, pow_add, hq, ← pow_mul, mul_comm n 2]
    have hW : 4 * N * d ^ 2 = (q - 1) * ((a * (q + 1) - 1) ^ 2 + q ^ 2) := by
      have hq0 : q ^ 4 ≠ 0 := pow_ne_zero _ (by omega)
      apply mul_left_cancel₀ hq0
      rw [h3j] at hN
      linear_combination hN
    have hcop : IsCoprime (d ^ 2) (q - 1) := by
      rw [hd, ← pow_mul, hq]; exact isCoprime_three_pow_sub_one hn _
    have hdW : d ^ 2 ∣ (a * (q + 1) - 1) ^ 2 + q ^ 2 :=
      hcop.dvd_of_dvd_mul_left ⟨4 * N, by linear_combination -hW⟩
    have hdq2 : d ^ 2 ∣ q ^ 2 := pow_dvd_pow_of_dvd hdq 2
    have hdw : d ∣ a * (q + 1) - 1 :=
      (Int.pow_dvd_pow_iff two_ne_zero).mp ((dvd_add_left hdq2).mp hdW)
    have hda : d ∣ a - 1 := by
      have : a - 1 = (a * (q + 1) - 1) - a * q := by ring
      rw [this]
      exact dvd_sub hdw (dvd_mul_of_dvd_right hdq a)
    rw [h3j] at hlow
    exact bound_aux hq3 hd3 ha hda (by nlinarith)

theorem cx_arith {n j : ℕ} {q s N : ℤ} (hq : q = 3 ^ n) (hn : 1 ≤ n) (hj2 : 2 * n ≤ j)
    (hj : j ≤ 3 * n) (hN : 2 * 3 ^ j * N = q * (q - 1) * (q ^ 3 + q - (q + 1) * s))
    (hlow : 1 + (1 - s) ^ 2 + s ^ 2 ≤ 3 ^ j) :
    (j = 2 * n ∧ s = 0) ∨ (2 * n < j ∧ s = q) := by
  have hq3 : 3 ≤ q := by
    rw [hq]; calc (3 : ℤ) = 3 ^ 1 := by norm_num
      _ ≤ 3 ^ n := pow_le_pow_right₀ (by norm_num) hn
  obtain ⟨t, ht⟩ : ∃ t, j = 2 * n + t := ⟨j - 2 * n, by omega⟩
  have htn : t ≤ n := by omega
  set d : ℤ := 3 ^ t with hd
  have hd1 : 1 ≤ d := by rw [hd]; exact one_le_pow₀ (by norm_num)
  have hdq : d ∣ q := by rw [hq, hd]; exact pow_dvd_pow 3 htn
  have h3j : (3 : ℤ) ^ j = q ^ 2 * d := by rw [ht, pow_add, hq, ← pow_mul, mul_comm n 2]
  rw [h3j] at hN hlow
  have hN' : q * d * (2 * N) = (q - 1) * (q ^ 3 + q - (q + 1) * s) := by
    have : q ≠ 0 := by omega
    apply mul_left_cancel₀ this
    linear_combination hN
  have hcop : IsCoprime (q * d) (q - 1) := by
    rw [hd, hq, ← pow_add]; exact isCoprime_three_pow_sub_one hn _
  have hdiv : q * d ∣ q ^ 3 + q - (q + 1) * s :=
    hcop.dvd_of_dvd_mul_left ⟨2 * N, by linear_combination -hN'⟩
  have hqs : q ∣ s := by
    have h1 : q ∣ (q + 1) * s := by
      have h2 : q ∣ q ^ 3 + q - (q + 1) * s := (dvd_mul_right q d).trans hdiv
      have h3 : q ∣ q ^ 3 + q := ⟨q ^ 2 + 1, by ring⟩
      have := dvd_sub h3 h2
      simpa using this
    have hc : IsCoprime q (q + 1) := ⟨-1, 1, by ring⟩
    exact hc.dvd_of_dvd_mul_left h1
  obtain ⟨a, rfl⟩ := hqs
  have hda : d ∣ a - 1 := by
    have h1 : q * d ∣ q * (q ^ 2 + 1 - (q + 1) * a) := by
      have : q ^ 3 + q - (q + 1) * (q * a) = q * (q ^ 2 + 1 - (q + 1) * a) := by ring
      rwa [this] at hdiv
    have h2 : d ∣ q ^ 2 + 1 - (q + 1) * a :=
      (mul_dvd_mul_iff_left (show q ≠ 0 by omega)).mp h1
    have h3 : d ∣ q * (q - a) := dvd_mul_of_dvd_left hdq _
    have := dvd_sub h3 h2
    have e : q * (q - a) - (q ^ 2 + 1 - (q + 1) * a) = a - 1 := by ring
    rwa [e] at this
  rcases Nat.eq_zero_or_pos t with ht0 | htpos
  · left
    refine ⟨by omega, ?_⟩
    rw [ht0, pow_zero] at hd
    rw [hd, mul_one] at hlow
    by_contra hne
    have ha0 : a ≠ 0 := by rintro rfl; simp at hne
    have h1 : q ^ 2 ≤ (q * a) ^ 2 := by
      rw [mul_pow]
      have : 1 ≤ a ^ 2 := by
        have := sq_pos_of_ne_zero ha0
        omega
      nlinarith
    have h2 : 1 ≤ (1 - q * a) ^ 2 := by
      have : 1 - q * a ≠ 0 := by
        intro h0
        have : q * a = 1 := by linarith
        have := Int.eq_one_or_neg_one_of_mul_eq_one this
        omega
      have := sq_pos_of_ne_zero this
      omega
    linarith
  · right
    refine ⟨by omega, ?_⟩
    by_contra hne
    have ha1 : a ≠ 1 := by rintro rfl; exact hne (mul_one q)
    have hd3 : 3 ≤ d := by
      rw [hd]; calc (3 : ℤ) = 3 ^ 1 := by norm_num
        _ ≤ 3 ^ t := pow_le_pow_right₀ (by norm_num) htpos
    have hb : d ≤ |a - 1| :=
      Int.le_of_dvd (abs_pos.mpr (sub_ne_zero.mpr ha1)) ((dvd_abs _ _).mpr hda)
    have hab : |a - 1| ≤ |a| + 1 := by
      calc |a - 1| ≤ |a| + |(1 : ℤ)| := abs_sub _ _
        _ = |a| + 1 := by simp
    have h2 : 2 ≤ |a| := by omega
    have hsq : a ^ 2 = |a| ^ 2 := (sq_abs a).symm
    have hneg : -(q * a) ≥ -(|a| * q) := by
      have := le_abs_self a
      nlinarith
    set b := |a| with hbdef
    have hdb : d ≤ b + 1 := by omega
    have hl : 2 * b ^ 2 * q ^ 2 - 2 * b * q + 2 ≤ q ^ 2 * (b + 1) := by
      have k1 : q ^ 2 * d ≤ q ^ 2 * (b + 1) := by
        have : 0 ≤ q ^ 2 := sq_nonneg q
        nlinarith
      nlinarith
    have k2 : q * (2 * b ^ 2 - b - 1) - 2 * b > 0 := by
      have k0 : (q - 3) * (2 * b ^ 2 - b - 1) ≥ 0 := mul_nonneg (by omega) (by nlinarith)
      nlinarith
    have k3 := mul_pos (show (0 : ℤ) < q by omega) k2
    nlinarith

end CFSG.Walter.WardLocal
