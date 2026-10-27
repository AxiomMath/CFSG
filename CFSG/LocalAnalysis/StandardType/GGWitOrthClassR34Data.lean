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
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.LinearAlgebra.Matrix.Cartan.Basic
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

namespace CFSG.StandardType.ZS

@[expose] def owR34_wA5 : Fin 4 → ZMod 3 := ![1, 1, 1, 2]

@[expose] def owR34_aA5 : Fin 5 → Fin 4 → ZMod 3 :=
  ![![0, 0, 1, 0], ![0, 1, 1, 1], ![0, 1, 0, 0], ![1, 1, 0, 1], ![1, 0, 0, 0]]

@[expose] def owR34_XA5 : Fin 15 → Fin 4 → ZMod 3 :=
  ![![0, 0, 1, 0], ![0, 1, 1, 1], ![0, 1, 0, 0], ![1, 1, 0, 1], ![1, 0, 0, 0], ![0, 1, 2, 1], ![0, 2, 1, 1], ![1, 2, 0, 1], ![2, 1, 0, 1], ![0, 2, 2, 1], ![1, 0, 1, 2], ![2, 2, 0, 1], ![1, 0, 2, 2], ![2, 0, 1, 2], ![2, 0, 2, 2]]

@[expose] def owR34_reflect (w a v : Fin 4 → ZMod 3) : Fin 4 → ZMod 3 :=
  fun k => v k - ((2 * (1 : ZMod 3)⁻¹) * ∑ j, w j * (v j * a j)) * a k

theorem owR34_normA5 : ∀ i : Fin 5,
    ∑ k, owR34_wA5 k * (owR34_aA5 i k * owR34_aA5 i k) = 1 := by
  decide +kernel

theorem owR34_cartanA5 : ∀ i j : Fin 5,
    (2 * (1 : ZMod 3)⁻¹) * ∑ k, owR34_wA5 k * (owR34_aA5 j k * owR34_aA5 i k) =
      (CartanMatrix.A 5 i j : ZMod 3) := by
  decide +kernel

theorem owR34_normXA5 : ∀ k : Fin 15,
    ∑ i, owR34_wA5 i * (owR34_XA5 k i * owR34_XA5 k i) = 1 := by
  decide +kernel

theorem owR34_coverA5 : ∀ y : Fin 4 → ZMod 3,
    ∑ k, owR34_wA5 k * (y k * y k) = 1 →
      ∃ k : Fin 15, y = owR34_XA5 k ∨ y = -owR34_XA5 k := by
  decide +kernel

theorem owR34_chainA5_0 :
    owR34_XA5 5 = owR34_reflect owR34_wA5 (owR34_aA5 1) (owR34_XA5 0) := by
  decide +kernel

theorem owR34_chainA5_1 :
    owR34_XA5 6 = owR34_reflect owR34_wA5 (owR34_aA5 2) (owR34_XA5 1) := by
  decide +kernel

theorem owR34_chainA5_2 :
    owR34_XA5 7 = owR34_reflect owR34_wA5 (owR34_aA5 3) (owR34_XA5 2) := by
  decide +kernel

theorem owR34_chainA5_3 :
    owR34_XA5 8 = owR34_reflect owR34_wA5 (owR34_aA5 4) (owR34_XA5 3) := by
  decide +kernel

theorem owR34_chainA5_4 :
    owR34_XA5 9 = owR34_reflect owR34_wA5 (owR34_aA5 2) (owR34_XA5 5) := by
  decide +kernel

theorem owR34_chainA5_5 :
    owR34_XA5 10 = owR34_reflect owR34_wA5 (owR34_aA5 3) (owR34_XA5 6) := by
  decide +kernel

theorem owR34_chainA5_6 :
    owR34_XA5 11 = owR34_reflect owR34_wA5 (owR34_aA5 4) (owR34_XA5 7) := by
  decide +kernel

theorem owR34_chainA5_7 :
    owR34_XA5 12 = owR34_reflect owR34_wA5 (owR34_aA5 3) (owR34_XA5 9) := by
  decide +kernel

theorem owR34_chainA5_8 :
    owR34_XA5 13 = owR34_reflect owR34_wA5 (owR34_aA5 4) (owR34_XA5 10) := by
  decide +kernel

theorem owR34_chainA5_9 :
    owR34_XA5 14 = owR34_reflect owR34_wA5 (owR34_aA5 4) (owR34_XA5 12) := by
  decide +kernel

theorem owR34_zmod3_eq_one_or_two : ∀ x : ZMod 3, x ≠ 0 → x = 1 ∨ x = 2 := by
  decide +kernel

end CFSG.StandardType.ZS

end
