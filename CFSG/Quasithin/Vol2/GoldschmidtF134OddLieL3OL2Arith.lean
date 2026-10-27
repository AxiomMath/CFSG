module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.Quasithin.H13.NQCore.L2Odd

theorem exists_sq_eq {p : ℕ} (hp : Odd p) : ∃ c : ℕ, p ^ 2 = 2 * c + 1 := by
  obtain ⟨k, rfl⟩ := hp
  exact ⟨2 * k * k + 2 * k, by ring⟩

theorem sq_sq_sub_one_div_two {p c : ℕ} (h : p ^ 2 = 2 * c + 1) :
    ((p ^ 2) ^ 2 - 1) / 2 = 2 * c * (c + 1) := by
  rw [h]
  have h1 : (2 * c + 1) ^ 2 = 2 * (2 * c * (c + 1)) + 1 := by ring
  omega

theorem not_dvd_of_sq {p c : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h : p ^ 2 = 2 * c + 1) :
    ¬ p ∣ c ∧ ¬ p ∣ c + 1 := by
  have hpp : p ∣ p ^ 2 := dvd_pow_self p two_ne_zero
  have hodd : ¬ p ∣ 2 := fun h2 =>
    hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2)
  constructor
  · intro hc
    have h1 : p ∣ 2 * c := Dvd.dvd.mul_left hc 2
    rw [h] at hpp
    have := (Nat.dvd_add_right h1).1 hpp
    exact hp.one_lt.ne' (Nat.dvd_one.1 this)
  · intro hc
    have h1 : p ∣ 2 * (c + 1) := Dvd.dvd.mul_left hc 2
    have h2 : p ^ 2 + 1 = 2 * (c + 1) := by omega
    rw [← h2] at h1
    have := (Nat.dvd_add_right hpp).1 h1
    exact hp.one_lt.ne' (Nat.dvd_one.1 this)

theorem not_two_pow_dvd {p c k m : ℕ} (hm : ¬ 2 ∣ m)
    (h : 2 ^ k * m = p ^ 2 * (2 * c * (c + 1))) : ¬ 2 ^ k ∣ c := by
  intro hc
  have h1 : 2 ^ (k + 1) ∣ p ^ 2 * (2 * c * (c + 1)) := by
    obtain ⟨u, rfl⟩ := hc
    exact ⟨p ^ 2 * (u * (2 ^ k * u + 1)), by ring⟩
  rw [← h, pow_succ] at h1
  have h2 : 2 ^ k * 2 ∣ 2 ^ k * m := h1
  exact hm ((Nat.mul_dvd_mul_iff_left (Nat.two_pow_pos k)).1 h2)

end CFSG.Quasithin.H13.NQCore.L2Odd
