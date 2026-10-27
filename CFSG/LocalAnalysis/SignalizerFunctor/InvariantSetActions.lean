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

universe actorUniverse pointUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {ActorType : Type actorUniverse} [Group ActorType]
variable {PointType : Type pointUniverse}

@[expose] def invariantSetPermutation
    (action : ActorType →* Equiv.Perm PointType) (points : Set PointType)
    (invariant : ∀ actor : ActorType, ∀ point : PointType,
      action actor point ∈ points ↔ point ∈ points) : ActorType →* Equiv.Perm points where
  toFun actor := (action actor).subtypePerm (invariant actor)
  map_one' := by
    apply Equiv.ext
    intro point
    apply Subtype.ext
    simp only [Equiv.Perm.subtypePerm_apply, map_one, Equiv.Perm.one_apply]
  map_mul' first second := by
    apply Equiv.ext
    intro point
    apply Subtype.ext
    simp only [Equiv.Perm.subtypePerm_apply, map_mul, Equiv.Perm.mul_apply]

theorem invariant_set_permutation_apply
    (action : ActorType →* Equiv.Perm PointType) (points : Set PointType)
    (invariant : ∀ actor : ActorType, ∀ point : PointType,
      action actor point ∈ points ↔ point ∈ points)
    (actor : ActorType) (point : points) :
    (invariantSetPermutation action points invariant actor point).val = action actor point.val := rfl

theorem commuting_permutation_preserves_fixed
    (first second : Equiv.Perm PointType) (commute : Commute first second) (point : PointType) :
    first (second point) = second point ↔ first point = point := by
  have interchange : first (second point) = second (first point) :=
    congrArg (fun permutation : Equiv.Perm PointType => permutation point) commute
  rw [interchange]
  exact second.injective.eq_iff

theorem commuting_permutation_unique_fixed_preserved
    (first second : Equiv.Perm PointType) (commute : Commute first second)
    (point : PointType) (fixed : first point = point)
    (unique : ∀ other : PointType, first other = other → other = point) : second point = point := by
  apply unique
  exact (commuting_permutation_preserves_fixed first second commute point).mpr fixed

end CFSG.SignalizerFunctor.Helpers
