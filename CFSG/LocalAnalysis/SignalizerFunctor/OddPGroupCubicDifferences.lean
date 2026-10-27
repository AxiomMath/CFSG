module

public import CFSG.Mathlib.GroupTheory.Basic
public import CFSG.LocalAnalysis.SignalizerFunctor.ClassTwoQuadraticPairing

public section

open scoped commutatorElement

universe groupUniverse actorUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType]

theorem odd_pgroup_square_eq_one (prime : ℕ) (prime_prime : prime.Prime) (odd_prime : prime ≠ 2)
    (pgroup : IsPGroup prime GroupType) (element : GroupType) (square : element ^ 2 = 1) : element = 1 := by
  obtain ⟨exponent, power⟩ := pgroup.exists_pow_pow_eq_one element
  have coprime : Nat.Coprime 2 (prime ^ exponent) :=
    ((Nat.coprime_primes Nat.prime_two prime_prime).mpr (Ne.symm odd_prime)).pow_right exponent
  exact (pow_eq_one_iff_of_coprime coprime).mp ⟨square, power⟩

theorem class_two_odd_pgroup_cubic_differences_commute
    (prime : ℕ) (prime_prime : prime.Prime) (odd_prime : prime ≠ 2)
    (pgroup : IsPGroup prime GroupType)
    (central : ∀ first second : GroupType, ⁅first, second⁆ ∈ Subgroup.center GroupType)
    (ActorType : Type actorUniverse) [Group ActorType] [IsMulCommutative ActorType]
    [MulDistribMulAction ActorType GroupType]
    (fixed_commutators : ∀ actorElement : ActorType, ∀ first second : GroupType,
      actorElement • ⁅first, second⁆ = ⁅first, second⁆)
    (element : GroupType)
    (cubic : ∀ first second third : ActorType,
      third • ((element⁻¹ * (first • element))⁻¹ * (second • (element⁻¹ * (first • element)))) =
        (element⁻¹ * (first • element))⁻¹ * (second • (element⁻¹ * (first • element))))
    (firstActor secondActor : ActorType) :
    Commute (element⁻¹ * (firstActor • element)) (element⁻¹ * (secondActor • element)) := by
  have commuting : ∀ value : GroupType,
      firstActor • (secondActor • value) = secondActor • (firstActor • value) := by
    intro value
    rw [← mul_smul, ← mul_smul, mul_comm' firstActor secondActor]
  have square := class_two_quadratic_pair_commutator_square central
    (MulDistribMulAction.toMulEquiv GroupType firstActor)
    (MulDistribMulAction.toMulEquiv GroupType secondActor)
    (fixed_commutators firstActor) (fixed_commutators secondActor) commuting element
    (cubic secondActor firstActor firstActor) (cubic secondActor firstActor secondActor)
    (cubic firstActor secondActor firstActor) (cubic firstActor secondActor secondActor)
  exact commutatorElement_eq_one_iff_commute.mp (odd_pgroup_square_eq_one prime prime_prime odd_prime
    pgroup _ square)

theorem class_two_odd_pgroup_cubic_difference_closure_abelian
    (prime : ℕ) (prime_prime : prime.Prime) (odd_prime : prime ≠ 2)
    (pgroup : IsPGroup prime GroupType)
    (central : ∀ first second : GroupType, ⁅first, second⁆ ∈ Subgroup.center GroupType)
    (ActorType : Type actorUniverse) [Group ActorType] [IsMulCommutative ActorType]
    [MulDistribMulAction ActorType GroupType]
    (fixed_commutators : ∀ actorElement : ActorType, ∀ first second : GroupType,
      actorElement • ⁅first, second⁆ = ⁅first, second⁆)
    (element : GroupType)
    (cubic : ∀ first second third : ActorType,
      third • ((element⁻¹ * (first • element))⁻¹ * (second • (element⁻¹ * (first • element)))) =
        (element⁻¹ * (first • element))⁻¹ * (second • (element⁻¹ * (first • element)))) :
    IsMulCommutative (Subgroup.closure (Set.range (fun actorElement : ActorType =>
      element⁻¹ * (actorElement • element)))) := by
  apply CFSG.subgroup_isMulCommutative_closure
  rintro _ ⟨firstActor, rfl⟩ _ ⟨secondActor, rfl⟩
  exact (class_two_odd_pgroup_cubic_differences_commute prime prime_prime odd_prime pgroup central ActorType
    fixed_commutators element cubic firstActor secondActor).eq

end CFSG.SignalizerFunctor.Helpers
