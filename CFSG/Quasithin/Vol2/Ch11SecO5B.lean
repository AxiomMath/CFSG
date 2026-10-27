module

public import Mathlib.Data.Nat.Factors
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecG.O5

theorem three_pow_mod_sixteen (d : ℕ) : 3 ^ d % 16 = 3 ^ (d % 4) % 16 := by
  conv_lhs => rw [← Nat.div_add_mod d 4, pow_add, pow_mul]
  rw [Nat.mul_mod, Nat.pow_mod (3 ^ 4)]
  norm_num

theorem three_pow_mod_eight (d : ℕ) : 3 ^ d % 8 = 3 ^ (d % 2) % 8 := by
  conv_lhs => rw [← Nat.div_add_mod d 2, pow_add, pow_mul]
  rw [Nat.mul_mod, Nat.pow_mod (3 ^ 2)]
  norm_num

theorem two_pow_add_one_ne_three_pow {k d : ℕ} (hk : 4 ≤ k) : 2 ^ k + 1 ≠ 3 ^ d := by
  intro h
  have h16 : 2 ^ k % 16 = 0 := Nat.mod_eq_zero_of_dvd (by simpa using Nat.pow_dvd_pow 2 hk)
  have h1 : 3 ^ (d % 4) % 16 = 1 := by
    rw [← three_pow_mod_sixteen, ← h]
    omega
  have hd : d % 4 = 0 := by
    have : d % 4 < 4 := Nat.mod_lt _ (by norm_num)
    interval_cases hd4 : d % 4 <;> simp_all
  have h5 : 3 ^ d % 5 = 1 := by
    rw [← Nat.div_add_mod d 4, hd, add_zero, pow_mul, Nat.pow_mod]
    norm_num
  have h25 : 5 ∣ 2 ^ k := by omega
  have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_five h25)
  omega

theorem two_pow_ne_three_pow_add_one {k d : ℕ} (hk : 3 ≤ k) : 2 ^ k ≠ 3 ^ d + 1 := by
  intro h
  have h8 : 2 ^ k % 8 = 0 := Nat.mod_eq_zero_of_dvd (by simpa using Nat.pow_dvd_pow 2 hk)
  have h3 : 3 ^ (d % 2) % 8 = 7 := by
    rw [← three_pow_mod_eight]
    omega
  have : d % 2 < 2 := Nat.mod_lt _ (by norm_num)
  interval_cases hd2 : d % 2 <;> simp_all

theorem eq_pow_of_prime_dvd {n q : ℕ} (hn : n ≠ 0) (h : ∀ d : ℕ, d.Prime → d ∣ n → d = q) :
    ∃ a : ℕ, n = q ^ a :=
  ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd hn fun hd hdn => h _ hd hdn⟩

theorem exists_prime_five_le_dvd {p : ℕ} (hp : p.Prime) (h11 : 11 ≤ p) (h17 : p ≠ 17) :
    ∃ r : ℕ, r.Prime ∧ 5 ≤ r ∧ (r ∣ p - 1 ∨ r ∣ p + 1) := by
  by_contra hne'
  have hne : ∀ r : ℕ, r.Prime → 5 ≤ r → ¬ r ∣ p - 1 ∧ ¬ r ∣ p + 1 := fun r hr h5 =>
    ⟨fun h => hne' ⟨r, hr, h5, Or.inl h⟩, fun h => hne' ⟨r, hr, h5, Or.inr h⟩⟩
  have hsmall : ∀ m : ℕ, (m ∣ p - 1 ∨ m ∣ p + 1) → ∀ d : ℕ, d.Prime → d ∣ m → d = 2 ∨ d = 3 :=
    fun m hm d hd hdm => by
      by_contra h23
      have h5 := hd.five_le_of_ne_two_of_ne_three (fun h => h23 (Or.inl h))
        (fun h => h23 (Or.inr h))
      rcases hm with hm | hm
      · exact (hne d hd h5).1 (hdm.trans hm)
      · exact (hne d hd h5).2 (hdm.trans hm)
  have hp3 : ¬ 3 ∣ p := fun h => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h
    omega
  by_cases hA : 3 ∣ p - 1
  ·
    have hB : ¬ 3 ∣ p + 1 := fun h => by omega
    obtain ⟨a, ha⟩ := eq_pow_of_prime_dvd (n := p + 1) (q := 2) (by omega) fun d hd hdn => by
      rcases hsmall _ (Or.inr dvd_rfl) d hd hdn with rfl | rfl
      · rfl
      · exact absurd hdn hB
    have ha4 : 4 ≤ a := by
      by_contra h4
      have : 2 ^ a ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have h4 : 4 ∣ p + 1 := ha ▸ (Nat.pow_dvd_pow 2 (by omega : 2 ≤ a))
    obtain ⟨b, hb⟩ := eq_pow_of_prime_dvd (n := (p - 1) / 2) (q := 3) (by omega) fun d hd hdn => by
      rcases hsmall _ (Or.inl (Nat.div_dvd_of_dvd (by omega))) d hd hdn with rfl | rfl
      · exfalso
        obtain ⟨c, hc⟩ := hdn
        omega
      · rfl
    have e : 2 ^ (a - 1) = 3 ^ b + 1 := by
      have : 2 ^ a = 2 * 2 ^ (a - 1) := by
        rw [← pow_succ']
        congr 1
        omega
      omega
    exact two_pow_ne_three_pow_add_one (by omega) e
  ·
    obtain ⟨a, ha⟩ := eq_pow_of_prime_dvd (n := p - 1) (q := 2) (by omega) fun d hd hdn => by
      rcases hsmall _ (Or.inl dvd_rfl) d hd hdn with rfl | rfl
      · rfl
      · exact absurd hdn hA
    have ha4 : 4 ≤ a := by
      by_contra h4
      have : 2 ^ a ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have h4 : 4 ∣ p - 1 := ha ▸ (Nat.pow_dvd_pow 2 (by omega : 2 ≤ a))
    obtain ⟨b, hb⟩ := eq_pow_of_prime_dvd (n := (p + 1) / 2) (q := 3) (by omega) fun d hd hdn => by
      rcases hsmall _ (Or.inr (Nat.div_dvd_of_dvd (by omega))) d hd hdn with rfl | rfl
      · exfalso
        obtain ⟨c, hc⟩ := hdn
        omega
      · rfl
    have e : 2 ^ (a - 1) + 1 = 3 ^ b := by
      have : 2 ^ a = 2 * 2 ^ (a - 1) := by
        rw [← pow_succ']
        congr 1
        omega
      omega
    rcases Nat.lt_or_ge (a - 1) 4 with h3 | h3
    · have ha5 : a = 4 := by omega
      subst ha5
      omega
    · exact two_pow_add_one_ne_three_pow h3 e

end CFSG.Quasithin.Vol2.Ch11.SecG.O5
