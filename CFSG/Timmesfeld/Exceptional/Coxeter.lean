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
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Timmesfeld.Moufang

variable {G : Type*} [Group G]

theorem braid_of_mul_pow_three {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (h : (a * b) ^ 3 = 1) : a * b * a = b * a * b := by
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have h' : a * b * a * (b * a * b) = 1 := by
    rw [← h]; simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  rw [eq_inv_of_mul_eq_one_left h', mul_inv_rev, mul_inv_rev, ha', hb', mul_assoc]

theorem mul_mul_pow_four_eq_one_of_pow_three {u v c : G} (hu : u * u = 1) (hv : v * v = 1)
    (hc : c * c = 1) (huv : Commute u v) (h1 : (u * c) ^ 3 = 1) (h2 : (v * c) ^ 3 = 1) :
    (u * v * c) ^ 4 = 1 := by
  have bu : c * u * c = u * c * u := (braid_of_mul_pow_three hu hc h1).symm
  have bv : c * v * c = v * c * v := (braid_of_mul_pow_three hv hc h2).symm
  have huvu : u * v * u = v := by rw [huv.eq, mul_assoc, hu, mul_one]
  have hvuv : v * u * v = u := by rw [← huv.eq, mul_assoc, hv, mul_one]
  have e1 : u * v * (c * u * c) = c * v * c * (u * v) := by
    rw [bu, bv]
    calc u * v * (u * c * u) = (u * v * u) * c * u := by group
      _ = v * c * u := by rw [huvu]
      _ = v * c * (v * u * v) := by rw [hvuv]
      _ = v * c * v * (u * v) := by group
  have e2 : u * v * (c * v * c) = c * u * c * (u * v) := by
    rw [bu, bv]
    calc u * v * (v * c * v) = u * (v * v) * c * v := by group
      _ = u * c * v := by rw [hv, mul_one]
      _ = u * c * (u * u) * v := by rw [hu, mul_one]
      _ = u * c * u * (u * v) := by group
  have hw2 : u * v * (u * v) = 1 := by
    rw [show u * v * (u * v) = u * v * u * v by group, huvu, hv]
  have hu'2 : c * u * c * (c * u * c) = 1 := by
    rw [show c * u * c * (c * u * c) = c * u * (c * c) * u * c by group, hc, mul_one,
      show c * u * u * c = c * (u * u) * c by group, hu, mul_one, hc]
  have hv'2 : c * v * c * (c * v * c) = 1 := by
    rw [show c * v * c * (c * v * c) = c * v * (c * c) * v * c by group, hc, mul_one,
      show c * v * v * c = c * (v * v) * c by group, hv, mul_one, hc]
  have hsq : (u * v * c) ^ 2 = u * v * (c * u * c) * (c * v * c) := by
    rw [pow_two]
    calc u * v * c * (u * v * c) = u * v * c * u * (c * c) * v * c := by
          rw [hc, mul_one]; group
      _ = u * v * (c * u * c) * (c * v * c) := by group
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hsq, pow_two]
  calc u * v * (c * u * c) * (c * v * c) * (u * v * (c * u * c) * (c * v * c))
      = u * v * (c * u * c) * ((c * v * c) * (u * v)) * (c * u * c) * (c * v * c) := by group
    _ = u * v * (c * u * c) * (u * v * (c * u * c)) * (c * u * c) * (c * v * c) := by rw [← e1]
    _ = u * v * (c * u * c) * (u * v) * ((c * u * c) * (c * u * c)) * (c * v * c) := by group
    _ = u * v * ((c * u * c) * (u * v)) * (c * v * c) := by rw [hu'2, mul_one]; group
    _ = u * v * (u * v * (c * v * c)) * (c * v * c) := by rw [← e2]
    _ = (u * v * (u * v)) * ((c * v * c) * (c * v * c)) := by group
    _ = 1 := by rw [hw2, hv'2, one_mul]

theorem mul_mul_eq_one_of_pow_three_of_odd {u v c : G} (hu : u * u = 1) (hv : v * v = 1)
    (hc : c * c = 1) (huv : Commute u v) (h1 : (u * c) ^ 3 = 1) (h2 : (v * c) ^ 3 = 1)
    (hodd : Odd (orderOf (u * v * c))) : u * v * c = 1 := by
  have h4 := mul_mul_pow_four_eq_one_of_pow_three hu hv hc huv h1 h2
  have hdvd : orderOf (u * v * c) ∣ 2 ^ 2 := orderOf_dvd_of_pow_eq_one (by simpa using h4)
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  rcases k with _ | k
  · exact orderOf_eq_one_iff.1 (by simpa using hk)
  · rw [hk, pow_succ] at hodd
    exact absurd hodd (by simp [Nat.odd_mul])

theorem false_of_orderOf_three_three_of_line {u v c : G} (hu : u * u = 1) (hv : v * v = 1)
    (hc : c * c = 1) (huv : Commute u v) (h1 : orderOf (u * c) = 3)
    (h2 : orderOf (v * c) = 3) (hodd : Odd (orderOf (u * v * c))) : False := by
  have h1' : (u * c) ^ 3 = 1 := by rw [← h1]; exact pow_orderOf_eq_one _
  have h2' : (v * c) ^ 3 = 1 := by rw [← h2]; exact pow_orderOf_eq_one _
  have h := mul_mul_eq_one_of_pow_three_of_odd hu hv hc huv h1' h2' hodd
  have hc' : c = v * u := by
    rw [eq_inv_of_mul_eq_one_right h, mul_inv_rev, inv_eq_of_mul_eq_one_right hu,
      inv_eq_of_mul_eq_one_right hv]
  have huc : u * c = v := by rw [hc', ← mul_assoc, huv.eq, mul_assoc, hu, mul_one]
  rw [huc] at h1
  have hdvd : orderOf v ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hv)
  rw [h1] at hdvd
  exact absurd hdvd (by norm_num)

end CFSG.Timmesfeld.Moufang
