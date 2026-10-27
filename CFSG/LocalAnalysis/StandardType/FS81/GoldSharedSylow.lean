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

namespace CFSG.StandardType.FrameRoute.FS81

@[expose] def GoldExclusionSylow : Prop :=
  ∀ (X : Type) [Group X] [Finite X], (∀ N : Subgroup X, N.Normal → Odd (Nat.card N) → N = ⊥) →
    ∀ (P : Sylow 2 X) (A : Subgroup X), A ≤ (P : Subgroup X) → IsMulCommutative A →
      (∀ a ∈ A, ∀ g : X, g⁻¹ * a * g ∈ (P : Subgroup X) → g⁻¹ * a * g ∈ A) →
        A.Normal ∨ ∃ R T₀ : Subgroup X, A ≤ T₀ ∧ T₀ ≤ R ∧ R ≤ Subgroup.normalizer (A : Set X) ∧
          (∀ n ∈ Subgroup.normalizer (A : Set X), ∀ r ∈ R, n * r * n⁻¹ ∈ R) ∧
          (∀ r ∈ R, ∀ t ∈ T₀, r * t * r⁻¹ ∈ T₀) ∧ IsPGroup 2 T₀ ∧ Odd (T₀.relIndex R) ∧
          ¬ R ≤ T₀

end CFSG.StandardType.FrameRoute.FS81

end
