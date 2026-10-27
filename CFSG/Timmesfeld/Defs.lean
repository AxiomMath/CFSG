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

namespace CFSG.Timmesfeld

variable {G : Type*} [Group G]

@[expose] def IsRootInvolutionSet (D : Set G) : Prop :=
  (∀ d ∈ D, orderOf d = 2) ∧
  (∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) = 2 ∨ orderOf (d * e) = 4 ∨ Odd (orderOf (d * e))) ∧
  (∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) = 4 → (d * e) ^ 2 ∈ D)

@[expose] def rootSet (D : Set G) (d : G) : Set G :=
  {e | e ∈ D ∧ ∀ f ∈ D, Commute e f ↔ Commute d f}

structure Hyp (G : Type*) [Group G] (D : Set G) : Prop where
  finite : Finite G
  isClass : ∃ d₀ : G, D = {g | IsConj d₀ g}
  root : IsRootInvolutionSet D
  gen : Subgroup.closure D = ⊤
  oddCore : ∀ N : Subgroup G, N.Normal → Odd (Nat.card N) → N = ⊥
  twoCore : ∀ N : Subgroup G, N.Normal → IsPGroup 2 N → N = ⊥
  nondeg : ∃ d ∈ D, ∃ e ∈ D, orderOf (d * e) = 4

end CFSG.Timmesfeld
