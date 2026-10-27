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

universe fieldUniverse vectorUniverse actorUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {FieldType : Type fieldUniverse} [Field FieldType]
variable {VectorType : Type vectorUniverse} [AddCommGroup VectorType] [Module FieldType VectorType]
variable {ActorType : Type actorUniverse} [Group ActorType]

theorem invariant_linear_submodule_map
    (action : ActorType →* (VectorType ≃ₗ[FieldType] VectorType))
    (subspace : Submodule FieldType VectorType)
    (invariant : ∀ actor : ActorType, ∀ vector ∈ subspace, action actor vector ∈ subspace)
    (actor : ActorType) : subspace.map (action actor).toLinearMap = subspace := by
  apply le_antisymm
  · rintro vector ⟨source, source_mem, rfl⟩
    exact invariant actor source source_mem
  · intro vector vector_mem
    refine ⟨action actor⁻¹ vector, invariant actor⁻¹ vector vector_mem, ?_⟩
    simp

def invariantLinearRestriction
    (action : ActorType →* (VectorType ≃ₗ[FieldType] VectorType))
    (subspace : Submodule FieldType VectorType)
    (invariant : ∀ actor : ActorType, ∀ vector ∈ subspace, action actor vector ∈ subspace) :
    ActorType →* (subspace ≃ₗ[FieldType] subspace) where
  toFun actor := (action actor).ofSubmodules subspace subspace
    (invariant_linear_submodule_map action subspace invariant actor)
  map_one' := by
    ext vector
    simp only [LinearEquiv.ofSubmodules_apply, map_one, LinearEquiv.coe_one, id_eq]
  map_mul' first second := by
    ext vector
    simp only [LinearEquiv.ofSubmodules_apply, map_mul, LinearEquiv.mul_apply]

theorem invariant_linear_restriction_apply
    (action : ActorType →* (VectorType ≃ₗ[FieldType] VectorType))
    (subspace : Submodule FieldType VectorType)
    (invariant : ∀ actor : ActorType, ∀ vector ∈ subspace, action actor vector ∈ subspace)
    (actor : ActorType) (vector : subspace) :
    (invariantLinearRestriction action subspace invariant actor vector).val = action actor vector.val :=
  LinearEquiv.ofSubmodules_apply _ _ _

def invariantLinearQuotient
    (action : ActorType →* (VectorType ≃ₗ[FieldType] VectorType))
    (subspace : Submodule FieldType VectorType)
    (invariant : ∀ actor : ActorType, ∀ vector ∈ subspace, action actor vector ∈ subspace) :
    ActorType →* ((VectorType ⧸ subspace) ≃ₗ[FieldType] (VectorType ⧸ subspace)) where
  toFun actor := Submodule.Quotient.equiv subspace subspace (action actor)
    (invariant_linear_submodule_map action subspace invariant actor)
  map_one' := by
    ext vector
    obtain ⟨representative, rfl⟩ := subspace.mkQ_surjective vector
    simp
  map_mul' first second := by
    ext vector
    obtain ⟨representative, rfl⟩ := subspace.mkQ_surjective vector
    simp

theorem invariant_linear_quotient_apply
    (action : ActorType →* (VectorType ≃ₗ[FieldType] VectorType))
    (subspace : Submodule FieldType VectorType)
    (invariant : ∀ actor : ActorType, ∀ vector ∈ subspace, action actor vector ∈ subspace)
    (actor : ActorType) (vector : VectorType) :
    invariantLinearQuotient action subspace invariant actor (subspace.mkQ vector) =
      subspace.mkQ (action actor vector) := by
  simp [invariantLinearQuotient]

end CFSG.SignalizerFunctor.Helpers
