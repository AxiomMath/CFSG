module

public import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148W

private theorem sub_one_core (x : ℕ) (h4 : x * x ≠ 4) (h1 : x * x % 3 = 1) :
    ∃ n, 1 < n ∧ n ∣ x * x - 1 ∧ ¬ 3 ∣ n := by
  have hr : x % 3 = 1 ∨ x % 3 = 2 := by
    rcases (by omega : x % 3 = 0 ∨ x % 3 = 1 ∨ x % 3 = 2) with h | h | h
    · rw [Nat.mul_mod, h] at h1
      omega
    · exact Or.inl h
    · exact Or.inr h
  have hx2 : x ≠ 2 := by
    rintro rfl
    exact h4 rfl
  rcases hr with hr | hr
  · refine ⟨x + 1, by omega, ?_, by omega⟩
    obtain ⟨y, rfl⟩ : ∃ y, x = y + 1 := ⟨x - 1, by omega⟩
    exact Dvd.intro y (Nat.eq_sub_of_add_eq (by ring))
  · obtain ⟨y, rfl⟩ : ∃ y, x = y + 1 := ⟨x - 1, by omega⟩
    exact ⟨y, by omega, Dvd.intro (y + 1 + 1) (Nat.eq_sub_of_add_eq (by ring)), by omega⟩

private theorem two_pow_mod_eighty (m : ℕ) :
    2 ^ (m + 4) % 80 = 16 ∨ 2 ^ (m + 4) % 80 = 32 ∨
      2 ^ (m + 4) % 80 = 64 ∨ 2 ^ (m + 4) % 80 = 48 := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    have e : 2 ^ (m + 1 + 4) = 2 ^ (m + 4) * 2 := by ring
    rw [e]
    omega

private theorem three_pow_mod_eighty (j : ℕ) :
    3 ^ j % 80 = 1 ∨ 3 ^ j % 80 = 3 ∨ 3 ^ j % 80 = 9 ∨ 3 ^ j % 80 = 27 := by
  induction j with
  | zero => norm_num
  | succ j ih =>
    rw [pow_succ]
    omega

private theorem two_pow_add_one_ne_three_pow {f j : ℕ} (hf : 4 ≤ f) (h : 2 ^ f + 1 = 3 ^ j) :
    False := by
  obtain ⟨m, rfl⟩ : ∃ m, f = m + 4 := ⟨f - 4, by omega⟩
  have := two_pow_mod_eighty m
  have := three_pow_mod_eighty j
  omega

theorem exists_coprime_three_dvd_sub_one {p f : ℕ} (hp : p.Prime) (h2 : 2 < p ^ f)
    (h4 : p ^ f ≠ 4) (h1 : p ^ f % 3 = 1) : ∃ n, 1 < n ∧ n ∣ p ^ f - 1 ∧ ¬ 3 ∣ n := by
  rcases hp.eq_two_or_odd' with rfl | hodd
  · obtain ⟨k, rfl⟩ : ∃ k, f = 2 * k := by
      rcases Nat.even_or_odd' f with ⟨k, hk | hk⟩
      · exact ⟨k, hk⟩
      · exfalso
        subst hk
        have e : 2 ^ (2 * k + 1) = 4 ^ k * 2 := by
          rw [pow_succ, pow_mul]
          norm_num
        have : 4 ^ k % 3 = 1 := by
          rw [Nat.pow_mod]
          norm_num
        omega
    have e : 2 ^ (2 * k) = 2 ^ k * 2 ^ k := by
      rw [two_mul, pow_add]
    rw [e] at h4 h1 ⊢
    exact sub_one_core (2 ^ k) h4 h1
  · refine ⟨2, by norm_num, ?_, by norm_num⟩
    have : p ^ f % 2 = 1 := Nat.odd_iff.mp hodd.pow
    omega

theorem exists_coprime_three_dvd_add_one {p f : ℕ} (hp : p.Prime) (h2 : 2 < p ^ f)
    (h8 : p ^ f ≠ 8) (h1 : p ^ f % 3 = 2) : ∃ n, 1 < n ∧ n ∣ p ^ f + 1 ∧ ¬ 3 ∣ n := by
  rcases hp.eq_two_or_odd' with rfl | hodd
  · have hodd3 : f % 2 = 1 := by
      by_contra hc
      obtain ⟨k, rfl⟩ : ∃ k, f = 2 * k := ⟨f / 2, by omega⟩
      have e : 2 ^ (2 * k) = 4 ^ k := by
        rw [pow_mul]
        norm_num
      have : 4 ^ k % 3 = 1 := by
        rw [Nat.pow_mod]
        norm_num
      omega
    have hf : 4 ≤ f := by
      by_contra hc
      have hlt : f < 4 := by omega
      interval_cases f <;> simp_all
    obtain ⟨e, m, hm, hfac⟩ :=
      Nat.exists_eq_pow_mul_and_not_dvd (by positivity : 2 ^ f + 1 ≠ 0) 3 (by norm_num)
    have hm1 : m ≠ 1 := by
      rintro rfl
      rw [mul_one] at hfac
      exact two_pow_add_one_ne_three_pow hf hfac
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hfac
      omega
    refine ⟨m, by omega, ?_, hm⟩
    rw [hfac]
    exact dvd_mul_left m _
  · refine ⟨2, by norm_num, ?_, by norm_num⟩
    have : p ^ f % 2 = 1 := Nat.odd_iff.mp hodd.pow
    omega

theorem exists_field_divisor_plus {q₀ : ℕ} (h1 : q₀ % 3 = 1) (h2 : 2 ≤ q₀) :
    ∃ n, 1 < n ∧ n ∣ q₀ ^ 3 - 1 ∧ ¬ 3 ∣ n ∧ ¬ n ∣ q₀ - 1 ∧ ¬ n ∣ q₀ ^ 2 - 1 := by
  obtain ⟨t, rfl⟩ : ∃ t, q₀ = 3 * t + 1 := ⟨q₀ / 3, by omega⟩
  have ht : 1 ≤ t := by omega
  refine ⟨3 * t ^ 2 + 3 * t + 1, by omega, Dvd.intro (9 * t) ?_, by omega, ?_, ?_⟩
  · apply Nat.eq_sub_of_add_eq
    ring
  · intro h
    have e : 3 * t + 1 - 1 = 3 * t := by omega
    rw [e] at h
    have := Nat.le_of_dvd (by omega) h
    omega
  · intro h
    have e : (3 * t + 1) ^ 2 - 1 = 9 * t ^ 2 + 6 * t := by
      apply Nat.sub_eq_of_eq_add
      ring
    rw [e] at h
    have h1' : 3 * t ^ 2 + 3 * t + 1 ∣ (3 * t ^ 2 + 3 * t + 1) + t * (9 * t ^ 2 + 6 * t) :=
      dvd_add (dvd_refl _) (Dvd.dvd.mul_left h t)
    have key : (3 * t ^ 2 + 3 * t + 1) + t * (9 * t ^ 2 + 6 * t)
        = 1 + 3 * t * (3 * t ^ 2 + 3 * t + 1) := by
      ring
    rw [key] at h1'
    have h2' : 3 * t ^ 2 + 3 * t + 1 ∣ 3 * t * (3 * t ^ 2 + 3 * t + 1) := dvd_mul_left _ _
    have h3' := (Nat.dvd_add_left h2').mp h1'
    have := Nat.dvd_one.mp h3'
    omega

theorem exists_field_divisor_minus {q₀ : ℕ} (h1 : q₀ % 3 = 2) (h2 : 2 < q₀) :
    ∃ n, 1 < n ∧ n ∣ q₀ ^ 3 + 1 ∧ ¬ 3 ∣ n ∧ ¬ n ∣ q₀ ^ 2 - 1 ∧ ¬ n ∣ q₀ ^ 4 - 1 := by
  obtain ⟨t, rfl⟩ : ∃ t, q₀ = 3 * t + 2 := ⟨q₀ / 3, by omega⟩
  have ht : 1 ≤ t := by omega
  refine ⟨3 * t ^ 2 + 3 * t + 1, by omega, Dvd.intro (9 * (t + 1)) ?_, by omega, ?_, ?_⟩
  · ring
  · intro h
    have e : (3 * t + 2) ^ 2 - 1 = 3 * (3 * t ^ 2 + 3 * t + 1) + 3 * t := by
      apply Nat.sub_eq_of_eq_add
      ring
    rw [e] at h
    have h' := (Nat.dvd_add_right (dvd_mul_left (3 * t ^ 2 + 3 * t + 1) 3)).mp h
    have := Nat.le_of_dvd (by omega) h'
    omega
  · intro h
    have e4 : (3 * t + 2) ^ 4 - 1 = 81 * t ^ 4 + 216 * t ^ 3 + 216 * t ^ 2 + 96 * t + 15 := by
      apply Nat.sub_eq_of_eq_add
      ring
    rw [e4] at h
    have hM : 3 * t ^ 2 + 3 * t + 1 ∣
        81 * t ^ 4 + 216 * t ^ 3 + 216 * t ^ 2 + 96 * t + 15 + (3 * t + 3) :=
      Dvd.intro (3 * (9 * t ^ 2 + 15 * t + 6)) (by ring)
    have h3 := (Nat.dvd_add_right h).mp hM
    have h5 : 3 * t ^ 2 + 3 * t + 1 ∣ t * (3 * t + 3) := Dvd.dvd.mul_left h3 t
    have h6 : 3 * t ^ 2 + 3 * t + 1 ∣ t * (3 * t + 3) + 1 := Dvd.intro 1 (by ring)
    have := Nat.dvd_one.mp ((Nat.dvd_add_right h5).mp h6)
    omega

end CFSG.RankThree.PartTwo.Sec14.Ronan148W
