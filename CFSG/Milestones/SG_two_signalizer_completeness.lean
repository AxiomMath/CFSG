module

import CFSG.LocalAnalysis.SolvableSignalizer.Completeness
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
public import Mathlib.Order.CompletePartialOrder
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

universe u v w

namespace CFSG.SolvableSignalizer

theorem _root_.CFSG.Milestones.sg_two_signalizer_completeness
    (G : Type) [Group G] [Finite G]
    (A : Type) [CommGroup A] [Finite A] (hexp : ∀ a : A, a ^ 2 = 1) (hcard : 8 ≤ Nat.card A)
    (α : A →* MulAut G) (θ : A → Subgroup G)
    (hinv : ∀ a : A, a ≠ 1 → ∀ b : A, (θ a).map (α b).toMonoidHom = θ a)
    (hsolv : ∀ a : A, a ≠ 1 → Group.IsSolvable (θ a))
    (hodd : ∀ a : A, a ≠ 1 → Odd (Nat.card (θ a)))
    (hcent : ∀ a : A, a ≠ 1 → ∀ g ∈ θ a, α a g = g)
    (hbal : ∀ a b : A, a ≠ 1 → b ≠ 1 → ∀ g ∈ θ a, α b g = g → g ∈ θ b) :
    let Θ : Subgroup G := ⨆ (a : A) (_ : a ≠ 1), θ a
    (∀ b : A, Θ.map (α b).toMonoidHom = Θ) ∧ Group.IsSolvable Θ ∧ Odd (Nat.card Θ) ∧
      ∀ a : A, a ≠ 1 → ∀ g : G, (g ∈ Θ ∧ α a g = g ↔ g ∈ θ a) :=
  two_signalizer_completeness G A hexp hcard α θ hinv hsolv hodd hcent hbal

end CFSG.SolvableSignalizer
