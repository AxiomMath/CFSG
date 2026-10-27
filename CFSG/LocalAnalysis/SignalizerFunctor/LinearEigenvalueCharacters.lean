module

public import CFSG.LocalAnalysis.SignalizerFunctor.ProjectiveLinearActions
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ReduceModChar

public section

universe fieldUniverse vectorUniverse actorUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {FieldType : Type fieldUniverse} [Field FieldType]
variable {VectorType : Type vectorUniverse} [AddCommGroup VectorType] [Module FieldType VectorType]
variable {ActorType : Type actorUniverse} [Group ActorType]

noncomputable def linearEigenvalueCharacter
    (action : ActorType →* (VectorType ≃ₗ[FieldType] VectorType))
    (vector : VectorType) (nonzero : vector ≠ 0)
    (invariant : ∀ actor : ActorType, ∃ scalar : FieldType, action actor vector = scalar • vector) :
    ActorType →* FieldTypeˣ where
  toFun actor := Units.mk0 (Classical.choose (invariant actor)) (by
    intro zero
    have image_zero := Classical.choose_spec (invariant actor)
    rw [zero, zero_smul] at image_zero
    exact nonzero ((action actor).injective (image_zero.trans (map_zero (action actor)).symm)))
  map_one' := by
    apply Units.ext
    apply smul_left_injective FieldType nonzero
    have eigen := Classical.choose_spec (invariant 1)
    simpa only [Units.val_mk0, Units.val_one, map_one, LinearEquiv.coe_one, id_eq, one_smul] using eigen.symm
  map_mul' first second := by
    apply Units.ext
    apply smul_left_injective FieldType nonzero
    have first_eigen := Classical.choose_spec (invariant first)
    have second_eigen := Classical.choose_spec (invariant second)
    have product_eigen := Classical.choose_spec (invariant (first * second))
    change Classical.choose (invariant (first * second)) • vector =
      (Classical.choose (invariant first) * Classical.choose (invariant second)) • vector
    calc
      _ = action (first * second) vector := product_eigen.symm
      _ = action first (action second vector) := by rw [map_mul, LinearEquiv.mul_apply]
      _ = (Classical.choose (invariant second) * Classical.choose (invariant first)) • vector := by
        conv_lhs => rw [second_eigen, map_smul, first_eigen, smul_smul]
      _ = _ := by rw [mul_comm]

theorem linear_eigenvalue_character_apply
    (action : ActorType →* (VectorType ≃ₗ[FieldType] VectorType))
    (vector : VectorType) (nonzero : vector ≠ 0)
    (invariant : ∀ actor : ActorType, ∃ scalar : FieldType, action actor vector = scalar • vector)
    (actor : ActorType) : action actor vector =
      (linearEigenvalueCharacter action vector nonzero invariant actor).val • vector :=
  Classical.choose_spec (invariant actor)

theorem linear_scalar_map_projective_identity
    (automorphism : VectorType ≃ₗ[FieldType] VectorType) (scalar : FieldType)
    (scalar_map : ∀ vector : VectorType, automorphism vector = scalar • vector) :
    projectiveLinearAction automorphism = 1 := by
  apply Equiv.ext
  intro point
  induction point using Projectivization.ind with
  | h vector nonzero =>
    exact (projective_linear_fixed_iff_eigenvector automorphism vector nonzero).mpr
      ⟨scalar, scalar_map vector⟩

theorem linear_projective_identity_equal_eigenvalues
    (automorphism : VectorType ≃ₗ[FieldType] VectorType)
    (first second : VectorType) (independent : LinearIndependent FieldType ![first, second])
    (first_scalar second_scalar : FieldType)
    (first_eigen : automorphism first = first_scalar • first)
    (second_eigen : automorphism second = second_scalar • second)
    (identity : projectiveLinearAction automorphism = 1) : first_scalar = second_scalar := by
  have sum_nonzero : first + second ≠ 0 := by
    intro zero
    have coefficients := independent.eq_zero_of_pair
      (show (1 : FieldType) • first + (1 : FieldType) • second = 0 by simpa only [one_smul] using zero)
    exact one_ne_zero coefficients.1
  have fixed : projectiveLinearAction automorphism (Projectivization.mk FieldType (first + second) sum_nonzero) =
      Projectivization.mk FieldType (first + second) sum_nonzero := by rw [identity]; rfl
  obtain ⟨scalar, eigen⟩ :=
    (projective_linear_fixed_iff_eigenvector automorphism (first + second) sum_nonzero).mp fixed
  rw [map_add, first_eigen, second_eigen, smul_add] at eigen
  have coefficients := independent.eq_of_pair eigen
  exact coefficients.1.trans coefficients.2.symm

noncomputable def linearTwoPointRatio
    (action : ActorType →* (VectorType ≃ₗ[FieldType] VectorType))
    (first second : VectorType) (first_nonzero : first ≠ 0) (second_nonzero : second ≠ 0)
    (first_invariant : ∀ actor : ActorType, ∃ scalar : FieldType, action actor first = scalar • first)
    (second_invariant : ∀ actor : ActorType, ∃ scalar : FieldType, action actor second = scalar • second) :
    ActorType →* FieldTypeˣ :=
  (linearEigenvalueCharacter action first first_nonzero first_invariant) *
    (linearEigenvalueCharacter action second second_nonzero second_invariant)⁻¹

theorem linear_two_point_ratio_kernel [FiniteDimensional FieldType VectorType]
    (dimension : Module.finrank FieldType VectorType = 2)
    (action : ActorType →* (VectorType ≃ₗ[FieldType] VectorType))
    (first second : VectorType) (first_nonzero : first ≠ 0) (second_nonzero : second ≠ 0)
    (independent : LinearIndependent FieldType ![first, second])
    (first_invariant : ∀ actor : ActorType, ∃ scalar : FieldType, action actor first = scalar • first)
    (second_invariant : ∀ actor : ActorType, ∃ scalar : FieldType, action actor second = scalar • second) :
    (linearTwoPointRatio action first second first_nonzero second_nonzero first_invariant second_invariant).ker =
      (projectiveLinearAction.comp action).ker := by
  ext actor
  let first_character := linearEigenvalueCharacter action first first_nonzero first_invariant
  let second_character := linearEigenvalueCharacter action second second_nonzero second_invariant
  have ratio_iff : actor ∈ (linearTwoPointRatio action first second first_nonzero second_nonzero
      first_invariant second_invariant).ker ↔ first_character actor = second_character actor := by
    change first_character actor * (second_character actor)⁻¹ = 1 ↔ _
    exact mul_inv_eq_one
  rw [ratio_iff]
  constructor
  · intro equal
    have first_eigen := linear_eigenvalue_character_apply action first first_nonzero first_invariant actor
    have second_eigen := linear_eigenvalue_character_apply action second second_nonzero second_invariant actor
    have agrees : Set.EqOn (action actor).toLinearMap
        (fun vector : VectorType => ((first_character actor).val • (1 : Module.End FieldType VectorType)) vector)
        (Set.range ![first, second]) := by
      rintro vector ⟨index, rfl⟩
      fin_cases index
      · exact first_eigen
      · change action actor second = (first_character actor).val • second
        rw [equal]
        exact second_eigen
    have span_top := independent.span_eq_top_of_card_eq_finrank (by simpa using dimension.symm)
    apply linear_scalar_map_projective_identity (action actor) (first_character actor).val
    intro vector
    exact LinearMap.eqOn_span (f := (action actor).toLinearMap)
      (g := (first_character actor).val • (1 : Module.End FieldType VectorType)) agrees
      (x := vector) (by rw [span_top]; exact Submodule.mem_top)
  · intro identity
    apply Units.ext
    exact linear_projective_identity_equal_eigenvalues (action actor) first second independent
      (first_character actor).val (second_character actor).val
      (linear_eigenvalue_character_apply action first first_nonzero first_invariant actor)
      (linear_eigenvalue_character_apply action second second_nonzero second_invariant actor) identity

end CFSG.SignalizerFunctor.Helpers
