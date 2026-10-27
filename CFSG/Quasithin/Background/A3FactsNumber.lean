module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
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
public import Mathlib.Tactic.ENatToNat
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
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Quasithin

namespace A3Facts

theorem three_pow_mod_eight (k : ℕ) : 3 ^ k % 8 = 1 ∨ 3 ^ k % 8 = 3 := by
  induction k with
  | zero => left; norm_num
  | succ k ih => rw [pow_succ]; rcases ih with h | h <;> omega

theorem exists_prime_dvd_two_pow_sub_one {f : ℕ} (hf : 3 ≤ f) :
    ∃ r : ℕ, r.Prime ∧ r ∣ 2 ^ f - 1 ∧ r ≠ 3 := by
  have h8 : 8 ∣ 2 ^ f := by
    obtain ⟨k, rfl⟩ : ∃ k, f = k + 3 := ⟨f - 3, by omega⟩
    rw [pow_add]; exact Dvd.intro_left _ rfl
  have hge : 8 ≤ 2 ^ f := Nat.le_of_dvd (by positivity) h8
  have hne : 2 ^ f - 1 ≠ 0 := by omega
  by_contra hcon
  push Not at hcon
  have hpow := Nat.eq_prime_pow_of_unique_prime_dvd (p := 3) hne
    (fun {d} hd hdvd => hcon d hd hdvd)
  have hmod : (2 ^ f - 1) % 8 = 7 := by omega
  have h3 := three_pow_mod_eight (2 ^ f - 1).primeFactorsList.length
  rw [← hpow] at h3
  omega

theorem two_pow_add_one_eq_three_pow {f k : ℕ} (h : 2 ^ f + 1 = 3 ^ k) (hf : 2 ≤ f) : f = 3 := by
  have h4 : 4 ∣ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ∣ 2 ^ f := pow_dvd_pow 2 hf
  rcases Nat.even_or_odd k with ⟨m, hm⟩ | ⟨m, hm⟩
  ·
    have hmpos : 1 ≤ 3 ^ m := Nat.one_le_pow _ _ (by norm_num)
    have h1 : (3 ^ m - 1) * (3 ^ m + 1) = 2 ^ f := by
      have : 3 ^ k = 3 ^ m * 3 ^ m := by rw [hm, pow_add]
      zify [hmpos]
      have h3k' : ((3:ℤ) ^ m) * (3 ^ m) = 2 ^ f + 1 := by exact_mod_cast (this.symm.trans h.symm)
      nlinarith
    have hd1 : 3 ^ m - 1 ∣ 2 ^ f := Dvd.intro _ h1
    have hd2 : 3 ^ m + 1 ∣ 2 ^ f := Dvd.intro_left _ h1
    obtain ⟨a, ha, ha'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd1
    obtain ⟨b, hb, hb'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd2
    have hdiff : 2 ^ b = 2 ^ a + 2 := by omega
    have hm1 : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with h0 | h0
      · subst h0
        simp at h1
        have : 4 ≤ 2 ^ f := Nat.le_of_dvd (by positivity) h4
        omega
      · exact h0
    have hge2 : 2 ≤ 3 ^ m - 1 := by
      have : 3 ≤ 3 ^ m := by
        calc 3 = 3 ^ 1 := by norm_num
          _ ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) hm1
      omega
    have ha1 : 1 ≤ a := by
      by_contra hcon
      have : a = 0 := by omega
      subst this
      simp at ha'
      omega
    have hb1 : 2 ≤ b := by
      by_contra hcon
      obtain rfl | rfl : b = 0 ∨ b = 1 := by omega
      · simp at hb'
      · simp at hb'
        omega
    have ha_eq : a = 1 := by
      by_contra hne1
      have ha2 : 2 ≤ a := by omega
      have h4a : 4 ∣ 2 ^ a := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ∣ 2 ^ a := pow_dvd_pow 2 ha2
      have h4b : 4 ∣ 2 ^ b := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ∣ 2 ^ b := pow_dvd_pow 2 hb1
      omega
    subst ha_eq
    have hb_eq : b = 2 := by
      have h22 : (2:ℕ) ^ b = 2 ^ 2 := by omega
      exact Nat.pow_right_injective (le_refl 2) h22
    subst hb_eq
    have h8 : 2 ^ f = 8 := by rw [← h1, ha', hb']; norm_num
    have h23 : (2:ℕ) ^ f = 2 ^ 3 := by simpa using h8
    exact Nat.pow_right_injective (le_refl 2) h23
  ·
    have hmod4 : 3 ^ k % 4 = 3 := by
      rw [hm, pow_succ, pow_mul]
      have h91 : (3 ^ 2) ^ m % 4 = 1 := by
        rw [Nat.pow_mod]; norm_num
      rw [Nat.mul_mod, h91]
    omega

theorem exists_prime_dvd_two_pow_add_one {f : ℕ} (hf : 2 ≤ f) (hf3 : f ≠ 3) :
    ∃ r : ℕ, r.Prime ∧ r ∣ 2 ^ f + 1 ∧ r ≠ 3 := by
  have hne : 2 ^ f + 1 ≠ 0 := Nat.succ_ne_zero _
  by_contra hcon
  push Not at hcon
  have hpow := Nat.eq_prime_pow_of_unique_prime_dvd (p := 3) hne
    (fun {d} hd hdvd => hcon d hd hdvd)
  exact hf3 (two_pow_add_one_eq_three_pow hpow hf)

end A3Facts

end CFSG.Quasithin
