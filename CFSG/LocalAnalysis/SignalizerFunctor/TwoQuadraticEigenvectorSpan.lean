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
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
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

universe fieldUniverse vectorUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {FieldType : Type fieldUniverse} [Field FieldType]
variable {VectorType : Type vectorUniverse} [AddCommGroup VectorType] [Module FieldType VectorType]

theorem quadratic_linear_square_apply (automorphism : VectorType ≃ₗ[FieldType] VectorType)
    (quadratic : (automorphism.toLinearMap - 1) ^ 2 = 0) (element : VectorType) :
    automorphism (automorphism element) = automorphism element + automorphism element - element := by
  have identity := congrArg (fun operator : Module.End FieldType VectorType => operator element) quadratic
  simp only [pow_two, Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply,
    LinearMap.zero_apply, map_sub] at identity
  change automorphism (automorphism element) - automorphism element - (automorphism element - element) = 0
    at identity
  apply sub_eq_zero.mp
  calc
    automorphism (automorphism element) - (automorphism element + automorphism element - element) =
        automorphism (automorphism element) - automorphism element - (automorphism element - element) := by abel
    _ = 0 := identity

theorem quadratic_linear_inverse_apply (automorphism : VectorType ≃ₗ[FieldType] VectorType)
    (quadratic : (automorphism.toLinearMap - 1) ^ 2 = 0) (element : VectorType) :
    automorphism⁻¹ element = element + element - automorphism element := by
  apply automorphism.injective
  change automorphism (automorphism.symm element) = automorphism (element + element - automorphism element)
  rw [LinearEquiv.apply_symm_apply, map_sub, map_add,
    quadratic_linear_square_apply automorphism quadratic]
  abel

theorem two_quadratic_eigenvector_span_invariant
    (first second : VectorType ≃ₗ[FieldType] VectorType)
    (first_quadratic : (first.toLinearMap - 1) ^ 2 = 0)
    (second_quadratic : (second.toLinearMap - 1) ^ 2 = 0)
    (eigenvalue : FieldType) (eigenvalue_nonzero : eigenvalue ≠ 0) (vector : VectorType)
    (eigenvector : second (first vector) = eigenvalue • vector) :
    let span := Submodule.span FieldType ({vector, first vector} : Set VectorType)
    (∀ element ∈ span, first element ∈ span) ∧
      (∀ element ∈ span, second element ∈ span) ∧
      (∀ element ∈ span, first⁻¹ element ∈ span) ∧
      (∀ element ∈ span, second⁻¹ element ∈ span) := by
  let span := Submodule.span FieldType ({vector, first vector} : Set VectorType)
  have vector_member : vector ∈ span := Submodule.subset_span (Set.mem_insert _ _)
  have first_vector_member : first vector ∈ span := Submodule.subset_span (Set.mem_insert_of_mem _ rfl)
  have second_formula : second vector = vector + vector - eigenvalue⁻¹ • first vector := by
    have equation := congrArg second eigenvector
    rw [quadratic_linear_square_apply second second_quadratic, eigenvector, map_smul] at equation
    calc
      second vector = eigenvalue⁻¹ • (eigenvalue • second vector) := by
        rw [smul_smul, inv_mul_cancel₀ eigenvalue_nonzero, one_smul]
      _ = eigenvalue⁻¹ • (eigenvalue • vector + eigenvalue • vector - first vector) := by rw [← equation]
      _ = vector + vector - eigenvalue⁻¹ • first vector := by
        rw [smul_sub, smul_add, smul_smul, inv_mul_cancel₀ eigenvalue_nonzero, one_smul]
  have first_stable : ∀ element ∈ span, first element ∈ span := by
    change span ≤ span.comap first.toLinearMap
    apply Submodule.map_le_iff_le_comap.mp
    apply (Submodule.map_span_le _ _ _).mpr
    intro element member
    change first element ∈ span
    rcases member with rfl | member
    · exact first_vector_member
    · have equality : element = first vector := member
      rw [equality, quadratic_linear_square_apply first first_quadratic]
      exact span.sub_mem (span.add_mem first_vector_member first_vector_member) vector_member
  have second_stable : ∀ element ∈ span, second element ∈ span := by
    change span ≤ span.comap second.toLinearMap
    apply Submodule.map_le_iff_le_comap.mp
    apply (Submodule.map_span_le _ _ _).mpr
    intro element member
    change second element ∈ span
    rcases member with rfl | member
    · rw [second_formula]
      exact span.sub_mem (span.add_mem vector_member vector_member) (span.smul_mem _ first_vector_member)
    · have equality : element = first vector := member
      rw [equality, eigenvector]
      exact span.smul_mem _ vector_member
  refine ⟨first_stable, second_stable, ?_, ?_⟩
  · intro element member
    rw [quadratic_linear_inverse_apply first first_quadratic]
    exact span.sub_mem (span.add_mem member member) (first_stable element member)
  · intro element member
    rw [quadratic_linear_inverse_apply second second_quadratic]
    exact span.sub_mem (span.add_mem member member) (second_stable element member)

theorem two_quadratic_irreducible_dimension_le_two [IsAlgClosed FieldType]
    [FiniteDimensional FieldType VectorType] [Nontrivial VectorType]
    (first second : VectorType ≃ₗ[FieldType] VectorType)
    (first_quadratic : (first.toLinearMap - 1) ^ 2 = 0)
    (second_quadratic : (second.toLinearMap - 1) ^ 2 = 0)
    (irreducible : ∀ subspace : Submodule FieldType VectorType,
      (∀ element ∈ subspace, first element ∈ subspace) →
      (∀ element ∈ subspace, second element ∈ subspace) → subspace = ⊥ ∨ subspace = ⊤) :
    Module.finrank FieldType VectorType ≤ 2 := by
  classical
  obtain ⟨eigenvalue, eigenvalue_exists⟩ :=
    Module.End.exists_eigenvalue (second.toLinearMap * first.toLinearMap)
  obtain ⟨vector, eigenvector⟩ := eigenvalue_exists.exists_hasEigenvector
  have vector_nonzero := eigenvector.2
  have eigen_eq : second (first vector) = eigenvalue • vector := eigenvector.apply_eq_smul
  have eigenvalue_nonzero : eigenvalue ≠ 0 := by
    intro zero
    rw [zero, zero_smul] at eigen_eq
    have first_zero := second.injective (eigen_eq.trans (map_zero second).symm)
    exact vector_nonzero (first.injective (first_zero.trans (map_zero first).symm))
  let span := Submodule.span FieldType ({vector, first vector} : Set VectorType)
  have invariant := two_quadratic_eigenvector_span_invariant first second first_quadratic second_quadratic
    eigenvalue eigenvalue_nonzero vector eigen_eq
  have span_top : span = ⊤ := by
    rcases irreducible span invariant.1 invariant.2.1 with zero | whole
    · have member : vector ∈ span := Submodule.subset_span (Set.mem_insert _ _)
      rw [zero, Submodule.mem_bot] at member
      exact (vector_nonzero member).elim
    · exact whole
  have bound := finrank_span_le_card (R := FieldType) ({vector, first vector} : Set VectorType)
  have card_bound : ({vector, first vector} : Set VectorType).toFinset.card ≤ 2 := by
    simp only [Set.toFinset_insert, Set.toFinset_singleton]
    exact (Finset.card_insert_le _ _).trans (by simp)
  change Module.finrank FieldType span ≤ _ at bound
  rw [span_top, finrank_top] at bound
  exact bound.trans card_bound

end CFSG.SignalizerFunctor.Helpers
