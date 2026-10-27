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

namespace CFSG.Quasithin.He8

open Matrix

@[expose] def IsMon (M : Matrix (Fin 2) (Fin 2) (ZMod 3)) : Prop :=
  (M 0 1 = 0 ∧ M 1 0 = 0 ∧ M 0 0 ≠ 0 ∧ M 1 1 ≠ 0) ∨ (M 0 0 = 0 ∧ M 1 1 = 0 ∧ M 0 1 ≠ 0 ∧ M 1 0 ≠ 0)

instance (M : Matrix (Fin 2) (Fin 2) (ZMod 3)) : Decidable (IsMon M) := by
  unfold IsMon
  infer_instance

theorem isMon_pow_four : ∀ M : Matrix (Fin 2) (Fin 2) (ZMod 3), IsMon M → M ^ 4 = 1 := by
  decide +kernel

theorem exists_mon_order_eight : ∀ U : Matrix (Fin 2) (Fin 2) (ZMod 3), U ^ 3 = 1 → U ≠ 1 →
    ∃ M : Matrix (Fin 2) (Fin 2) (ZMod 3), IsMon M ∧ (M * U) ^ 8 = 1 ∧ (M * U) ^ 4 ≠ 1 := by
  decide +kernel

end CFSG.Quasithin.He8
