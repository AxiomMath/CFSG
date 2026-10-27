module

public import CFSG.Quasithin.Vol2.Ch11SecO5B
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

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Quasithin.Vol2.Ch11.SecG.O5 (exists_prime_five_le_dvd)

theorem exists_prime_five_le_dvd_sq_sub_one {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p)
    (h5' : p ≠ 5) (h7 : p ≠ 7) (h17 : p ≠ 17) :
    ∃ r : ℕ, r.Prime ∧ 5 ≤ r ∧ r ∣ p ^ 2 - 1 := by
  have hp2 : p ^ 2 - 1 = (p + 1) * (p - 1) := by
    simpa using Nat.pow_two_sub_pow_two p 1
  by_cases h11 : 11 ≤ p
  · obtain ⟨r, hr, hr5, hd | hd⟩ := exists_prime_five_le_dvd hp h11 h17
    · exact ⟨r, hr, hr5, by rw [hp2]; exact dvd_mul_of_dvd_right hd (p + 1)⟩
    · exact ⟨r, hr, hr5, by rw [hp2]; exact dvd_mul_of_dvd_left hd (p - 1)⟩
  · have hlt : p < 11 := not_le.mp h11
    interval_cases p
    · exact absurd rfl h5'
    · exact absurd hp (by norm_num)
    · exact absurd rfl h7
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
