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

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

@[expose] def YCoverPlus (Y : Type) [Group Y] : Prop :=
  ∀ t : Y, orderOf t = 3 → ∃ e f g : Y, orderOf e = 3 ∧ orderOf f = 3 ∧ e * f = f * e ∧
    f ∉ Subgroup.zpowers e ∧ t ∈ Subgroup.closure ({e, f} : Set Y) ∧
    g * e = e * g ∧ g * f = f⁻¹ * g

@[expose] def YFix3Wit (Y : Type) [Group Y] : Prop :=
  ∀ s : Y, orderOf s = 7 → ∃ z : Y, orderOf z = 3 ∧ z * s = s * z

@[expose] def YFixClaim (Y : Type) [Group Y] : Prop :=
  ∀ β : MulAut Y, β ^ 3 = 1 → ∀ x : Y, orderOf x = 7 → β x = x →
    ∃ t : Y, t ^ 3 = 1 ∧ ∀ y : Y, β y = t * y * t⁻¹

end CFSG.LocalAnalysis.UniquenessCase.UCK
