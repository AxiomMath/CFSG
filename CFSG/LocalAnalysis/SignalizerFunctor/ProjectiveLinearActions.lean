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
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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

universe fieldUniverse vectorUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {FieldType : Type fieldUniverse} [Field FieldType]
variable {VectorType : Type vectorUniverse} [AddCommGroup VectorType] [Module FieldType VectorType]

def projectiveLinearAction :
    (VectorType ≃ₗ[FieldType] VectorType) →* Equiv.Perm (Projectivization FieldType VectorType) where
  toFun automorphism := {
    toFun := Projectivization.map automorphism.toLinearMap automorphism.injective
    invFun := Projectivization.map automorphism.symm.toLinearMap automorphism.symm.injective
    left_inv := by
      intro point
      have composition : automorphism.symm.toLinearMap ∘ₗ automorphism.toLinearMap = LinearMap.id := by
        ext vector
        exact automorphism.symm_apply_apply vector
      have mapped := congrFun (Projectivization.map_comp automorphism.toLinearMap automorphism.injective
        automorphism.symm.toLinearMap automorphism.symm.injective) point
      simpa only [composition, Projectivization.map_id, Function.comp_apply, id_eq] using mapped.symm
    right_inv := by
      intro point
      have composition : automorphism.toLinearMap ∘ₗ automorphism.symm.toLinearMap = LinearMap.id := by
        ext vector
        exact automorphism.apply_symm_apply vector
      have mapped := congrFun (Projectivization.map_comp automorphism.symm.toLinearMap
        automorphism.symm.injective automorphism.toLinearMap automorphism.injective) point
      simpa only [composition, Projectivization.map_id, Function.comp_apply, id_eq] using mapped.symm }
  map_one' := by
    apply Equiv.ext
    intro point
    change Projectivization.map (1 : VectorType ≃ₗ[FieldType] VectorType).toLinearMap
      (1 : VectorType ≃ₗ[FieldType] VectorType).injective point = point
    simpa only [LinearEquiv.coe_toLinearMap_one, id_eq] using
      congrFun (Projectivization.map_id (K := FieldType) (V := VectorType)) point
  map_mul' first second := by
    apply Equiv.ext
    intro point
    change Projectivization.map (first * second).toLinearMap (first * second).injective point =
      Projectivization.map first.toLinearMap first.injective
        (Projectivization.map second.toLinearMap second.injective point)
    exact congrFun (Projectivization.map_comp second.toLinearMap second.injective
      first.toLinearMap first.injective) point

theorem projective_linear_action_mk
    (automorphism : VectorType ≃ₗ[FieldType] VectorType)
    (vector : VectorType) (nonzero : vector ≠ 0) :
    projectiveLinearAction automorphism (Projectivization.mk FieldType vector nonzero) =
      Projectivization.mk FieldType (automorphism vector)
        (by simpa only [ne_eq, EmbeddingLike.map_eq_zero_iff] using nonzero) :=
  Projectivization.map_mk automorphism.toLinearMap automorphism.injective vector nonzero

theorem projective_linear_fixed_iff_eigenvector
    (automorphism : VectorType ≃ₗ[FieldType] VectorType)
    (vector : VectorType) (nonzero : vector ≠ 0) :
    projectiveLinearAction automorphism (Projectivization.mk FieldType vector nonzero) =
      Projectivization.mk FieldType vector nonzero ↔
      ∃ scalar : FieldType, automorphism vector = scalar • vector := by
  rw [projective_linear_action_mk, Projectivization.mk_eq_mk_iff']
  exact exists_congr (fun scalar : FieldType =>
    (eq_comm : scalar • vector = automorphism vector ↔ automorphism vector = scalar • vector))

theorem quadratic_linear_eigenvector_fixed
    (automorphism : VectorType ≃ₗ[FieldType] VectorType)
    (quadratic : (automorphism.toLinearMap - 1) ^ 2 = 0)
    (vector : VectorType) (nonzero : vector ≠ 0)
    (scalar : FieldType) (eigenvector : automorphism vector = scalar • vector) :
    automorphism vector = vector := by
  have square := congrArg (fun operator : Module.End FieldType VectorType => operator vector) quadratic
  have first_difference : (automorphism.toLinearMap - 1) vector = (scalar - 1) • vector := by
    change automorphism vector - vector = (scalar - 1) • vector
    rw [eigenvector, sub_smul, one_smul]
  have second_difference : (((automorphism.toLinearMap - 1) : Module.End FieldType VectorType) ^ 2) vector =
      ((scalar - 1) ^ 2) • vector := by
    rw [pow_two, Module.End.mul_apply, first_difference, map_smul, first_difference, smul_smul, pow_two]
  rw [second_difference, LinearMap.zero_apply] at square
  have scalar_one : scalar = 1 := by
    have scalar_square_zero := (smul_eq_zero.mp square).resolve_right nonzero
    exact sub_eq_zero.mp (eq_zero_of_pow_eq_zero scalar_square_zero)
  rw [eigenvector, scalar_one, one_smul]

theorem quadratic_projective_fixed_iff_linear_fixed
    (automorphism : VectorType ≃ₗ[FieldType] VectorType)
    (quadratic : (automorphism.toLinearMap - 1) ^ 2 = 0)
    (vector : VectorType) (nonzero : vector ≠ 0) :
    projectiveLinearAction automorphism (Projectivization.mk FieldType vector nonzero) =
      Projectivization.mk FieldType vector nonzero ↔ automorphism vector = vector := by
  rw [projective_linear_fixed_iff_eigenvector]
  constructor
  · rintro ⟨scalar, eigenvector⟩
    exact quadratic_linear_eigenvector_fixed automorphism quadratic vector nonzero scalar eigenvector
  · intro fixed
    exact ⟨1, by rwa [one_smul]⟩

theorem quadratic_projective_kernel_trivial
    (automorphism : VectorType ≃ₗ[FieldType] VectorType)
    (quadratic : (automorphism.toLinearMap - 1) ^ 2 = 0)
    (projective_identity : projectiveLinearAction automorphism = 1) : automorphism = 1 := by
  apply LinearEquiv.ext
  intro vector
  by_cases nonzero : vector = 0
  · simp [nonzero]
  · have fixed : projectiveLinearAction automorphism (Projectivization.mk FieldType vector nonzero) =
        Projectivization.mk FieldType vector nonzero := by rw [projective_identity]; rfl
    exact (quadratic_projective_fixed_iff_linear_fixed automorphism quadratic vector nonzero).mp fixed

end CFSG.SignalizerFunctor.Helpers
