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
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
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

universe fieldUniverse extensionUniverse vectorUniverse

namespace CFSG.SignalizerFunctor.Helpers

open scoped TensorProduct

variable {FieldType : Type fieldUniverse} [Field FieldType]
variable (ExtensionType : Type extensionUniverse) [Field ExtensionType] [Algebra FieldType ExtensionType]
variable {VectorType : Type vectorUniverse} [AddCommGroup VectorType] [Module FieldType VectorType]

def linearScalarExtension :
    (VectorType ≃ₗ[FieldType] VectorType) →*
      ((ExtensionType ⊗[FieldType] VectorType) ≃ₗ[ExtensionType] (ExtensionType ⊗[FieldType] VectorType)) where
  toFun := LinearEquiv.baseChange FieldType ExtensionType VectorType VectorType
  map_one' := LinearEquiv.baseChange_one _ _ _
  map_mul' := LinearEquiv.baseChange_mul _ _ _

theorem linear_scalar_extension_injective :
    Function.Injective (linearScalarExtension (FieldType := FieldType)
      (VectorType := VectorType) ExtensionType) := by
  intro first second equal
  have maps_equal : LinearMap.baseChange ExtensionType first.toLinearMap =
      LinearMap.baseChange ExtensionType second.toLinearMap := by
    simpa only [linearScalarExtension, MonoidHom.coe_mk, OneHom.coe_mk,
      LinearEquiv.coe_baseChange] using congrArg LinearEquiv.toLinearMap equal
  have original_equal := LinearMap.baseChangeHom_injective FieldType VectorType ExtensionType maps_equal
  exact LinearEquiv.toLinearMap_injective original_equal

theorem linear_scalar_extension_quadratic
    (automorphism : VectorType ≃ₗ[FieldType] VectorType)
    (quadratic : (automorphism.toLinearMap - 1) ^ 2 = 0) :
    ((linearScalarExtension ExtensionType automorphism).toLinearMap - 1) ^ 2 = 0 := by
  have extended := congrArg (LinearMap.baseChange ExtensionType) quadratic
  simpa only [pow_two, LinearMap.baseChange_mul, LinearMap.baseChange_sub,
    LinearMap.baseChange_one, LinearMap.baseChange_zero, linearScalarExtension,
    MonoidHom.coe_mk, OneHom.coe_mk, LinearEquiv.coe_baseChange] using extended

end CFSG.SignalizerFunctor.Helpers
