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

open Equiv

namespace Certificates

theorem perm_six_pow_four (t : Perm (Fin 6)) (h : t ^ 16 = 1) : t ^ 4 = 1 := by
  have h16 : orderOf t ∣ 16 := orderOf_dvd_of_pow_eq_one h
  refine orderOf_dvd_iff_pow_eq_one.mp ?_
  rw [← Perm.lcm_cycleType]
  refine Multiset.lcm_dvd.mpr fun n hn => ?_
  have hd : n ∣ 16 := (Perm.dvd_of_mem_cycleType hn).trans h16
  have hle : n ≤ 6 := (Perm.le_card_support_of_mem_cycleType hn).trans
    ((Finset.card_le_univ _).trans (by simp))
  have hpos : 0 < n := Nat.pos_of_dvd_of_pos hd (by norm_num)
  interval_cases n <;> omega

open Subgroup Equiv in
theorem certificate8145 : ∀ t : Perm (Fin 6), t ^ 16 = 1 → t ^ 4 = 1 := perm_six_pow_four

end Certificates
