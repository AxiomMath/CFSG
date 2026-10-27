module

public import CFSG.LocalAnalysis.SignalizerFunctor.CoprimeProjectiveEigenlines
public import Std.Tactic.BVDecide.Normalize.Prop

public section

universe fieldUniverse vectorUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {FieldType : Type fieldUniverse} [Field FieldType]
variable {VectorType : Type vectorUniverse} [AddCommGroup VectorType] [Module FieldType VectorType]

theorem distinct_eigenvalues_eigenvector_in_two_lines [FiniteDimensional FieldType VectorType]
    (dimension : Module.finrank FieldType VectorType = 2)
    (automorphism : VectorType ≃ₗ[FieldType] VectorType)
    (first second : VectorType) (first_nonzero : first ≠ 0) (second_nonzero : second ≠ 0)
    (independent : LinearIndependent FieldType ![first, second])
    (first_scalar second_scalar : FieldType) (distinct : first_scalar ≠ second_scalar)
    (first_eigen : automorphism first = first_scalar • first)
    (second_eigen : automorphism second = second_scalar • second)
    (vector : VectorType) (nonzero : vector ≠ 0)
    (scalar : FieldType) (eigen : automorphism vector = scalar • vector) :
    Projectivization.mk FieldType vector nonzero = Projectivization.mk FieldType first first_nonzero ∨
      Projectivization.mk FieldType vector nonzero = Projectivization.mk FieldType second second_nonzero := by
  have span_pair : Submodule.span FieldType ({first, second} : Set VectorType) = ⊤ := by
    have span := independent.span_eq_top_of_card_eq_finrank (by simpa using dimension.symm)
    have range_pair : Set.range ![first, second] = ({first, second} : Set VectorType) := by
      ext value
      constructor
      · rintro ⟨index, rfl⟩
        fin_cases index <;> simp
      · intro member
        rcases Set.mem_insert_iff.mp member with equal | member
        · exact ⟨0, equal.symm⟩
        · exact ⟨1, (Set.mem_singleton_iff.mp member).symm⟩
    rwa [range_pair] at span
  obtain ⟨first_coefficient, second_coefficient, decomposition⟩ :=
    Submodule.mem_span_pair.mp (show vector ∈ Submodule.span FieldType {first, second} from
      by rw [span_pair]; exact Submodule.mem_top)
  have image_eq : (first_coefficient * first_scalar) • first +
      (second_coefficient * second_scalar) • second =
      (scalar * first_coefficient) • first + (scalar * second_coefficient) • second := by
    calc
      _ = automorphism (first_coefficient • first + second_coefficient • second) := by
        rw [map_add, map_smul, map_smul, first_eigen, second_eigen, smul_smul, smul_smul]
      _ = scalar • (first_coefficient • first + second_coefficient • second) := by
        rw [decomposition, eigen]
      _ = _ := by rw [smul_add, smul_smul, smul_smul]
  have coefficient_eq := independent.eq_of_pair image_eq
  by_cases first_zero : first_coefficient = 0
  · right
    apply (Projectivization.mk_eq_mk_iff' _ _ _ _ _).mpr
    exact ⟨second_coefficient, by simpa only [first_zero, zero_smul, zero_add] using decomposition⟩
  · left
    have first_scalar_eq : first_scalar = scalar := by
      apply mul_left_cancel₀ first_zero
      simpa only [mul_comm scalar first_coefficient] using coefficient_eq.1
    have second_zero : second_coefficient = 0 := by
      by_contra not_zero
      have second_scalar_eq : second_scalar = scalar := by
        apply mul_left_cancel₀ not_zero
        simpa only [mul_comm scalar second_coefficient] using coefficient_eq.2
      exact distinct (first_scalar_eq.trans second_scalar_eq.symm)
    apply (Projectivization.mk_eq_mk_iff' _ _ _ _ _).mpr
    exact ⟨first_coefficient, by simpa only [second_zero, zero_smul, add_zero] using decomposition⟩

theorem semisimple_projective_fixed_exactly_two [IsAlgClosed FieldType]
    [FiniteDimensional FieldType VectorType] [Nontrivial VectorType]
    (dimension : Module.finrank FieldType VectorType = 2)
    (automorphism : VectorType ≃ₗ[FieldType] VectorType)
    (semisimple : Module.End.IsSemisimple automorphism.toLinearMap)
    (nonidentity : projectiveLinearAction automorphism ≠ 1) :
    ∃ first second : Projectivization FieldType VectorType, first ≠ second ∧
      ∀ point : Projectivization FieldType VectorType,
        projectiveLinearAction automorphism point = point ↔ point = first ∨ point = second := by
  obtain ⟨first, second, first_scalar, second_scalar, first_nonzero, second_nonzero,
    independent, first_eigen, second_eigen, scalar_distinct⟩ :=
    semisimple_projective_distinct_eigenlines dimension automorphism semisimple nonidentity
  refine ⟨Projectivization.mk FieldType first first_nonzero,
    Projectivization.mk FieldType second second_nonzero,
    projective_eigenline_distinct_of_independent first second first_nonzero second_nonzero independent, ?_⟩
  intro point
  constructor
  · intro fixed
    induction point using Projectivization.ind with
    | h vector nonzero =>
      obtain ⟨scalar, eigen⟩ := (projective_linear_fixed_iff_eigenvector automorphism vector nonzero).mp fixed
      exact distinct_eigenvalues_eigenvector_in_two_lines dimension automorphism first second first_nonzero
        second_nonzero independent first_scalar second_scalar scalar_distinct first_eigen second_eigen
        vector nonzero scalar eigen
  · rintro (rfl | rfl)
    · exact (projective_linear_fixed_iff_eigenvector automorphism first first_nonzero).mpr
        ⟨first_scalar, first_eigen⟩
    · exact (projective_linear_fixed_iff_eigenvector automorphism second second_nonzero).mpr
        ⟨second_scalar, second_eigen⟩

theorem coprime_order_projective_fixed_exactly_two [IsAlgClosed FieldType]
    [FiniteDimensional FieldType VectorType] [Nontrivial VectorType]
    (dimension : Module.finrank FieldType VectorType = 2)
    (prime : ℕ) [CharP FieldType prime]
    (automorphism : VectorType ≃ₗ[FieldType] VectorType)
    (exponent : ℕ) (coprime : ¬prime ∣ exponent) (power_one : automorphism ^ exponent = 1)
    (nonidentity : projectiveLinearAction automorphism ≠ 1) :
    ∃ first second : Projectivization FieldType VectorType, first ≠ second ∧
      ∀ point : Projectivization FieldType VectorType,
        projectiveLinearAction automorphism point = point ↔ point = first ∨ point = second :=
  semisimple_projective_fixed_exactly_two dimension automorphism
    (coprime_order_linear_semisimple prime automorphism exponent coprime power_one) nonidentity

end CFSG.SignalizerFunctor.Helpers
