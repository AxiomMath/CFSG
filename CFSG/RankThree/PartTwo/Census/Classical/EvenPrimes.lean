module

public import Mathlib.NumberTheory.Padics.PadicVal.Basic
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
import Mathlib.NumberTheory.Multiplicity
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.RankThree.PartTwo.Census

theorem odd_of_three_dvd_two_pow_add_one {f : ℕ} (h : 3 ∣ 2 ^ f + 1) : Odd f := by
  rw [← ZMod.natCast_eq_zero_iff] at h
  push_cast at h
  rw [pow_eq_pow_mod f (show (2 : ZMod 3) ^ 2 = 1 by decide)] at h
  rcases Nat.even_or_odd f with hf | hf
  · rw [Nat.even_iff.mp hf] at h
    exact absurd h (by decide)
  · exact hf

theorem mod_four_of_five_dvd_two_pow_add_one {f : ℕ} (h : 5 ∣ 2 ^ f + 1) : f % 4 = 2 := by
  rw [← ZMod.natCast_eq_zero_iff] at h
  push_cast at h
  rw [pow_eq_pow_mod f (show (2 : ZMod 5) ^ 4 = 1 by decide)] at h
  have h4 : f % 4 < 4 := Nat.mod_lt _ (by norm_num)
  interval_cases hf : f % 4 <;> first | rfl | exact absurd h (by decide)

theorem three_mul_lt_two_pow_add_one {f : ℕ} (hf : 4 ≤ f) : 3 * f < 2 ^ f + 1 := by
  induction f, hf using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [pow_succ]
    have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    omega

theorem three_pow_padicValNat_le {f : ℕ} (hf : Odd f) :
    3 ^ padicValNat 3 (2 ^ f + 1) ≤ 3 * f := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h := padicValNat.pow_add_pow (p := 3) (x := 2) (y := 1) (by decide) (by norm_num)
    (by norm_num) hf
  rw [one_pow, show (2 + 1 : ℕ) = 3 from rfl, padicValNat_self] at h
  rw [h, pow_add, pow_one]
  exact Nat.mul_le_mul_left 3 (Nat.le_of_dvd hf.pos pow_padicValNat_dvd)

theorem five_pow_padicValNat_le {m : ℕ} (hm : Odd m) :
    5 ^ padicValNat 5 (4 ^ m + 1) ≤ 5 * m := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h := padicValNat.pow_add_pow (p := 5) (x := 4) (y := 1) (by decide) (by norm_num)
    (by norm_num) hm
  rw [one_pow, show (4 + 1 : ℕ) = 5 from rfl, padicValNat_self] at h
  rw [h, pow_add, pow_one]
  exact Nat.mul_le_mul_left 5 (Nat.le_of_dvd hm.pos pow_padicValNat_dvd)

theorem odd_two_pow_add_one {f : ℕ} (hf : 1 ≤ f) : Odd (2 ^ f + 1) := by
  refine Even.add_one ?_
  exact (Nat.even_pow' (by omega)).mpr even_two

theorem eq_pow_padicValNat {n p : ℕ} (hp : p.Prime) (hn : n ≠ 0)
    (h : ∀ d, d.Prime → d ∣ n → d = p) : p ^ padicValNat p n = n := by
  have : Fact p.Prime := ⟨hp⟩
  have he := Nat.eq_prime_pow_of_unique_prime_dvd hn (fun hd hdn => h _ hd hdn)
  conv_lhs => rw [he]
  rw [padicValNat.prime_pow, ← he]

theorem exists_prime_seven_le_dvd_two_pow_add_one {f : ℕ} (hf : 4 ≤ f) :
    ∃ r, r.Prime ∧ 7 ≤ r ∧ r ∣ 2 ^ f + 1 := by
  by_contra hne
  push Not at hne
  have hodd := odd_two_pow_add_one (f := f) (by omega)
  have hlt := three_mul_lt_two_pow_add_one hf
  have hsmall : ∀ d, d.Prime → d ∣ 2 ^ f + 1 → d = 3 ∨ d = 5 := by
    intro d hd hdn
    have h7 : d < 7 := by
      by_contra h7
      exact hne d hd (by omega) hdn
    have h2 : d ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdn)
    interval_cases d <;> first | omega | exact absurd hd (by norm_num)
  rcases Nat.even_or_odd f with hfe | hfo
  ·
    have h5 : ∀ d, d.Prime → d ∣ 2 ^ f + 1 → d = 5 := by
      intro d hd hdn
      rcases hsmall d hd hdn with rfl | rfl
      · exact absurd (odd_of_three_dvd_two_pow_add_one hdn) (Nat.not_odd_iff_even.mpr hfe)
      · rfl
    have heq := eq_pow_padicValNat (by norm_num) (by omega) h5
    obtain ⟨d, hd, hdn⟩ := Nat.exists_prime_and_dvd (n := 2 ^ f + 1) (by
      have : 2 ≤ 2 ^ f := Nat.le_self_pow (by omega) 2
      omega)
    have h4 := mod_four_of_five_dvd_two_pow_add_one (h5 d hd hdn ▸ hdn)
    obtain ⟨m, rfl⟩ : ∃ m, f = 2 * m := ⟨f / 2, by omega⟩
    have hm : Odd m := Nat.odd_iff.mpr (by omega)
    have hle := five_pow_padicValNat_le hm
    rw [show (4 : ℕ) ^ m = 2 ^ (2 * m) by rw [pow_mul]; norm_num, heq] at hle
    omega
  · have h3 : ∀ d, d.Prime → d ∣ 2 ^ f + 1 → d = 3 := by
      intro d hd hdn
      rcases hsmall d hd hdn with rfl | rfl
      · rfl
      · have := mod_four_of_five_dvd_two_pow_add_one hdn
        have := Nat.odd_iff.mp hfo
        omega
    have heq := eq_pow_padicValNat Nat.prime_three (by omega) h3
    have hle := three_pow_padicValNat_le hfo
    rw [heq] at hle
    omega

theorem exists_prime_five_le_dvd_two_pow_add_one {f : ℕ} (hf : 2 ≤ f) (hf3 : f ≠ 3) :
    ∃ r, r.Prime ∧ 5 ≤ r ∧ r ∣ 2 ^ f + 1 := by
  rcases Nat.lt_or_ge f 4 with h4 | h4
  · obtain rfl : f = 2 := by omega
    exact ⟨5, by norm_num, le_rfl, by norm_num⟩
  · obtain ⟨r, hr, h7, hrd⟩ := exists_prime_seven_le_dvd_two_pow_add_one h4
    exact ⟨r, hr, by omega, hrd⟩

theorem exists_odd_prime_dvd_two_pow_add_one {f : ℕ} (hf : 1 ≤ f) :
    ∃ r, r.Prime ∧ r ≠ 2 ∧ r ∣ 2 ^ f + 1 := by
  obtain ⟨r, hr, hrd⟩ := Nat.exists_prime_and_dvd (n := 2 ^ f + 1) (by
    have : 2 ≤ 2 ^ f := Nat.le_self_pow (by omega) 2
    omega)
  refine ⟨r, hr, ?_, hrd⟩
  rintro rfl
  exact (Nat.not_even_iff_odd.mpr (odd_two_pow_add_one hf)) (even_iff_two_dvd.mpr hrd)

theorem three_pow_mod_eight (a : ℕ) : 3 ^ a % 8 = 1 ∨ 3 ^ a % 8 = 3 := by
  induction a with
  | zero => left; rfl
  | succ a ih =>
    rw [pow_succ, Nat.mul_mod]
    rcases ih with h | h <;> rw [h] <;> norm_num

theorem exists_prime_five_le_dvd_two_pow_sub_one {f : ℕ} (hf : 3 ≤ f) :
    ∃ r, r.Prime ∧ 5 ≤ r ∧ r ∣ 2 ^ f - 1 := by
  by_contra hne
  push Not at hne
  have h8 : 2 ^ f % 8 = 0 := by
    obtain ⟨k, rfl⟩ : ∃ k, f = k + 3 := ⟨f - 3, by omega⟩
    rw [pow_add]
    norm_num
  have hpos : 8 ≤ 2 ^ f := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have h3 : ∀ d, d.Prime → d ∣ 2 ^ f - 1 → d = 3 := by
    intro d hd hdn
    have h5 : d < 5 := by
      by_contra h5
      exact hne d hd (by omega) hdn
    have h2 : d ≠ 2 := by
      rintro rfl
      omega
    interval_cases d <;> first | omega | exact absurd hd (by norm_num)
  have heq := eq_pow_padicValNat Nat.prime_three (by omega) h3
  rcases three_pow_mod_eight (padicValNat 3 (2 ^ f - 1)) with h | h <;> omega

theorem exists_prime_ne_five_dvd_two_pow_sub_one {f : ℕ} (hf : 2 ≤ f) :
    ∃ r, r.Prime ∧ r ≠ 2 ∧ r ≠ 5 ∧ r ∣ 2 ^ f - 1 := by
  by_contra hne
  push Not at hne
  have h4 : 2 ^ f % 4 = 0 := by
    obtain ⟨k, rfl⟩ : ∃ k, f = k + 2 := ⟨f - 2, by omega⟩
    rw [pow_add]
    norm_num
  have hpos : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have h5 : ∀ d, d.Prime → d ∣ 2 ^ f - 1 → d = 5 := by
    intro d hd hdn
    by_contra h5
    refine hne d hd ?_ h5 hdn
    rintro rfl
    omega
  have heq := eq_pow_padicValNat (by norm_num) (by omega) h5
  have h1 : 5 ^ padicValNat 5 (2 ^ f - 1) % 4 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  omega

end CFSG.RankThree.PartTwo.Census
