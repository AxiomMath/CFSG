module

public import CFSG.LocalAnalysis.SignalizerFunctor.ProjectiveLinearActions
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ReduceModChar
public import Std.Tactic.BVDecide.Normalize.Prop

public section

universe fieldUniverse vectorUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {FieldType : Type fieldUniverse} [Field FieldType]
variable {VectorType : Type vectorUniverse} [AddCommGroup VectorType] [Module FieldType VectorType]

theorem characteristic_prime_power_root_one
    (prime : ℕ) (prime_prime : prime.Prime) [CharP FieldType prime]
    (scalar : FieldType) (exponent : ℕ) (power_one : scalar ^ (prime ^ exponent) = 1) :
    scalar = 1 := by
  let : Fact prime.Prime := ⟨prime_prime⟩
  have difference_power : (scalar - 1) ^ (prime ^ exponent) = 0 := by
    rw [sub_pow_char_pow, power_one, one_pow, sub_self]
  exact sub_eq_zero.mp (eq_zero_of_pow_eq_zero difference_power)

theorem linear_prime_power_eigenvector_fixed
    (prime : ℕ) (prime_prime : prime.Prime) [CharP FieldType prime]
    (automorphism : VectorType ≃ₗ[FieldType] VectorType)
    (exponent : ℕ) (power_one : automorphism ^ (prime ^ exponent) = 1)
    (vector : VectorType) (nonzero : vector ≠ 0)
    (scalar : FieldType) (eigenvector : automorphism vector = scalar • vector) :
    automorphism vector = vector := by
  have eigen : Module.End.HasEigenvector automorphism.toLinearMap scalar vector :=
    ⟨Module.End.mem_eigenspace_iff.mpr eigenvector, nonzero⟩
  have vector_power := eigen.pow_apply (prime ^ exponent)
  have operator_power : automorphism.toLinearMap ^ (prime ^ exponent) = 1 := by
    have mapped := congrArg
      (LinearEquiv.automorphismGroup.toLinearMapMonoidHom (R := FieldType) (M := VectorType)) power_one
    simpa only [map_pow, map_one, LinearEquiv.automorphismGroup.toLinearMapMonoidHom_apply] using mapped
  rw [operator_power, Module.End.one_apply] at vector_power
  have scalar_power : scalar ^ (prime ^ exponent) = 1 := by
    apply (smul_left_injective FieldType nonzero)
    simpa only [one_smul] using vector_power.symm
  rw [eigenvector, characteristic_prime_power_root_one prime prime_prime scalar exponent scalar_power,
    one_smul]

theorem prime_power_projective_fixed_iff_linear_fixed
    (prime : ℕ) (prime_prime : prime.Prime) [CharP FieldType prime]
    (automorphism : VectorType ≃ₗ[FieldType] VectorType)
    (exponent : ℕ) (power_one : automorphism ^ (prime ^ exponent) = 1)
    (vector : VectorType) (nonzero : vector ≠ 0) :
    projectiveLinearAction automorphism (Projectivization.mk FieldType vector nonzero) =
      Projectivization.mk FieldType vector nonzero ↔ automorphism vector = vector := by
  rw [projective_linear_fixed_iff_eigenvector]
  constructor
  · rintro ⟨scalar, eigenvector⟩
    exact linear_prime_power_eigenvector_fixed prime prime_prime automorphism exponent power_one
      vector nonzero scalar eigenvector
  · intro fixed
    exact ⟨1, by rwa [one_smul]⟩

theorem two_projective_points_span [FiniteDimensional FieldType VectorType]
    (dimension : Module.finrank FieldType VectorType = 2)
    (first second : Projectivization FieldType VectorType) (distinct : first ≠ second) :
    Submodule.span FieldType ({first.rep, second.rep} : Set VectorType) = ⊤ := by
  have independent := (Projectivization.linearIndependent_pair_iff_ne).mpr distinct
  have span := independent.span_eq_top_of_card_eq_finrank (by simpa using dimension.symm)
  have range_pair : Set.range ![first.rep, second.rep] = ({first.rep, second.rep} : Set VectorType) := by
    ext vector
    constructor
    · rintro ⟨index, rfl⟩
      fin_cases index <;> simp
    · intro member
      rcases Set.mem_insert_iff.mp member with equal | member
      · exact ⟨0, equal.symm⟩
      · exact ⟨1, (Set.mem_singleton_iff.mp member).symm⟩
  rwa [range_pair] at span

theorem linear_fixed_two_projective_representatives_identity [FiniteDimensional FieldType VectorType]
    (dimension : Module.finrank FieldType VectorType = 2)
    (automorphism : VectorType ≃ₗ[FieldType] VectorType)
    (first second : Projectivization FieldType VectorType) (distinct : first ≠ second)
    (first_fixed : automorphism first.rep = first.rep)
    (second_fixed : automorphism second.rep = second.rep) : automorphism = 1 := by
  have span := two_projective_points_span dimension first second distinct
  have agrees : Set.EqOn automorphism.toLinearMap (LinearMap.id : Module.End FieldType VectorType)
      ({first.rep, second.rep} : Set VectorType) := by
    intro vector member
    rcases Set.mem_insert_iff.mp member with equal | member
    · exact equal ▸ first_fixed
    · exact (Set.mem_singleton_iff.mp member) ▸ second_fixed
  apply LinearEquiv.ext
  intro vector
  exact LinearMap.eqOn_span agrees (by rw [span]; exact Submodule.mem_top)

theorem prime_power_projective_two_fixed_identity [FiniteDimensional FieldType VectorType]
    (dimension : Module.finrank FieldType VectorType = 2)
    (prime : ℕ) (prime_prime : prime.Prime) [CharP FieldType prime]
    (automorphism : VectorType ≃ₗ[FieldType] VectorType)
    (exponent : ℕ) (power_one : automorphism ^ (prime ^ exponent) = 1)
    (first second : Projectivization FieldType VectorType) (distinct : first ≠ second)
    (first_fixed : projectiveLinearAction automorphism first = first)
    (second_fixed : projectiveLinearAction automorphism second = second) : automorphism = 1 := by
  apply linear_fixed_two_projective_representatives_identity dimension automorphism first second distinct
  · apply (prime_power_projective_fixed_iff_linear_fixed prime prime_prime automorphism exponent
      power_one first.rep first.rep_nonzero).mp
    simpa only [Projectivization.mk_rep] using first_fixed
  · apply (prime_power_projective_fixed_iff_linear_fixed prime prime_prime automorphism exponent
      power_one second.rep second.rep_nonzero).mp
    simpa only [Projectivization.mk_rep] using second_fixed

theorem prime_power_projective_fixed_exists [IsAlgClosed FieldType]
    [FiniteDimensional FieldType VectorType] [Nontrivial VectorType]
    (automorphism : VectorType ≃ₗ[FieldType] VectorType) :
    ∃ point : Projectivization FieldType VectorType, projectiveLinearAction automorphism point = point := by
  obtain ⟨scalar, eigenvalue⟩ := Module.End.exists_eigenvalue automorphism.toLinearMap
  obtain ⟨vector, eigenvector⟩ := eigenvalue.exists_hasEigenvector
  refine ⟨Projectivization.mk FieldType vector eigenvector.2, ?_⟩
  exact (projective_linear_fixed_iff_eigenvector automorphism vector eigenvector.2).mpr
    ⟨scalar, eigenvector.apply_eq_smul⟩

theorem prime_power_projective_unique_fixed [IsAlgClosed FieldType]
    [FiniteDimensional FieldType VectorType] [Nontrivial VectorType]
    (dimension : Module.finrank FieldType VectorType = 2)
    (prime : ℕ) (prime_prime : prime.Prime) [CharP FieldType prime]
    (automorphism : VectorType ≃ₗ[FieldType] VectorType) (nonidentity : automorphism ≠ 1)
    (exponent : ℕ) (power_one : automorphism ^ (prime ^ exponent) = 1) :
    ∃! point : Projectivization FieldType VectorType, projectiveLinearAction automorphism point = point := by
  obtain ⟨point, fixed⟩ := prime_power_projective_fixed_exists automorphism
  refine ⟨point, fixed, ?_⟩
  intro other other_fixed
  by_contra distinct
  exact nonidentity (prime_power_projective_two_fixed_identity dimension prime prime_prime automorphism
    exponent power_one other point distinct other_fixed fixed)

end CFSG.SignalizerFunctor.Helpers
