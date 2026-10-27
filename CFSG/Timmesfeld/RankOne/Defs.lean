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

structure IsElemAbRankOne {X : Type*} [Group X] (A B : Subgroup X) : Prop where
  gen : A ⊔ B = ⊤
  ne : A ≠ B
  comm : ∀ a ∈ A, ∀ a' ∈ A, Commute a a'
  sq : ∀ a ∈ A, a * a = 1
  moufang : ∀ a ∈ A, a ≠ 1 → ∃ b ∈ B, b ≠ 1 ∧
    A.map (MulAut.conj b).toMonoidHom = B.map (MulAut.conj a).toMonoidHom
  moufang' : ∀ b ∈ B, b ≠ 1 → ∃ a ∈ A, a ≠ 1 ∧
    B.map (MulAut.conj a).toMonoidHom = A.map (MulAut.conj b).toMonoidHom

@[expose] def upperUnipotent (K : Type*) [Field K] :
    Subgroup (Matrix.SpecialLinearGroup (Fin 2) K) :=
  Subgroup.closure {g | ∃ t : K, (g : Matrix (Fin 2) (Fin 2) K) = !![1, t; 0, 1]}

@[expose] def lowerUnipotent (K : Type*) [Field K] :
    Subgroup (Matrix.SpecialLinearGroup (Fin 2) K) :=
  Subgroup.closure {g | ∃ t : K, (g : Matrix (Fin 2) (Fin 2) K) = !![1, 0; t, 1]}

end CFSG.Timmesfeld
