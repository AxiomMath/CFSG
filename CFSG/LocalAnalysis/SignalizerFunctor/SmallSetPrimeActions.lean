module

public import CFSG.LocalAnalysis.SignalizerFunctor.ProjectivePrimeElements
public import Mathlib.Data.Nat.Prime.Factorial

public section

universe pointUniverse fieldUniverse vectorUniverse

namespace CFSG.SignalizerFunctor.Helpers

theorem prime_power_permutation_small_identity
    {PointType : Type pointUniverse} [Finite PointType]
    (prime : ℕ) (prime_prime : prime.Prime) (small : Nat.card PointType < prime)
    (permutation : Equiv.Perm PointType) (exponent : ℕ)
    (power_one : permutation ^ (prime ^ exponent) = 1) : permutation = 1 := by
  have coprime := (prime_prime.coprime_factorial_of_lt small).pow_left exponent
  have cardinality := Nat.card_perm (α := PointType)
  have card_power : permutation ^ (Nat.card PointType).factorial = 1 := by
    rw [← cardinality]
    exact pow_card_eq_one'
  exact (pow_eq_one_iff_of_coprime coprime).mp ⟨power_one, card_power⟩

theorem prime_power_permutation_small_set_fixed
    {PointType : Type pointUniverse}
    (prime : ℕ) (prime_prime : prime.Prime)
    (permutation : Equiv.Perm PointType) (exponent : ℕ)
    (power_one : permutation ^ (prime ^ exponent) = 1)
    (points : Set PointType) (finite : points.Finite) (small : points.ncard < prime)
    (invariant : ∀ point : PointType, permutation point ∈ points ↔ point ∈ points) :
    ∀ point ∈ points, permutation point = point := by
  let _finite : Finite points := finite.to_subtype
  let restriction := permutation.subtypePerm invariant
  have restriction_power : restriction ^ (prime ^ exponent) = 1 := by
    dsimp only [restriction]
    simp only [Equiv.Perm.subtypePerm_pow, power_one]
    rfl
  have restriction_identity := prime_power_permutation_small_identity prime prime_prime
    (by simpa only [Nat.card_coe_set_eq] using small) restriction exponent restriction_power
  intro point member
  have fixed := congrArg (fun automorphism : Equiv.Perm points => (automorphism ⟨point, member⟩).val)
    restriction_identity
  exact fixed

variable {FieldType : Type fieldUniverse} [Field FieldType]
variable {VectorType : Type vectorUniverse} [AddCommGroup VectorType] [Module FieldType VectorType]

theorem prime_power_projective_two_set_identity [FiniteDimensional FieldType VectorType]
    (dimension : Module.finrank FieldType VectorType = 2)
    (prime : ℕ) (prime_prime : prime.Prime) (odd_prime : prime ≠ 2) [CharP FieldType prime]
    (automorphism : VectorType ≃ₗ[FieldType] VectorType)
    (exponent : ℕ) (power_one : automorphism ^ (prime ^ exponent) = 1)
    (first second : Projectivization FieldType VectorType) (distinct : first ≠ second)
    (invariant : ∀ point : Projectivization FieldType VectorType,
      projectiveLinearAction automorphism point ∈ ({first, second} : Set (Projectivization FieldType VectorType))
        ↔ point ∈ ({first, second} : Set (Projectivization FieldType VectorType))) :
    automorphism = 1 := by
  have projective_power : projectiveLinearAction automorphism ^ (prime ^ exponent) = 1 := by
    rw [← map_pow, power_one, map_one]
  have small : ({first, second} : Set (Projectivization FieldType VectorType)).ncard < prime := by
    rw [Set.ncard_pair distinct]
    have lower := prime_prime.two_le
    omega
  have fixed := prime_power_permutation_small_set_fixed prime prime_prime
    (projectiveLinearAction automorphism) exponent projective_power {first, second}
    (Set.finite_insert.mpr (Set.finite_singleton _)) small invariant
  exact prime_power_projective_two_fixed_identity dimension prime prime_prime automorphism exponent power_one
    first second distinct (fixed first (Set.mem_insert _ _)) (fixed second (Set.mem_insert_of_mem _ rfl))

end CFSG.SignalizerFunctor.Helpers
