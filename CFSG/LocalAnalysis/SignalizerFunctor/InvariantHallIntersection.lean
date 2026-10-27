module

public import CFSG.LocalAnalysis.SignalizerFunctor.FixedNormalizedPrimeHull

public section

universe actorUniverse groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {ActorType : Type actorUniverse} [Group ActorType]
variable {GroupType : Type groupUniverse} [Group GroupType]
variable [MulDistribMulAction ActorType GroupType]

@[expose] def invariantHallIntersection (primes : Set ℕ) : Subgroup GroupType :=
  ⨅ (hall : Subgroup GroupType)
    (_ : IsHallSubgroup primes hall ∧
      ∀ actorElement : ActorType, ∀ element ∈ hall, actorElement • element ∈ hall), hall

theorem invariant_hall_intersection_le (primes : Set ℕ) (hall : Subgroup GroupType)
    (hall_property : IsHallSubgroup primes hall)
    (invariant : ∀ actorElement : ActorType, ∀ element ∈ hall, actorElement • element ∈ hall) :
    invariantHallIntersection (ActorType := ActorType) primes ≤ hall :=
  (iInf_le _ hall).trans (iInf_le _ ⟨hall_property, invariant⟩)

theorem invariant_conjugate_of_fixed (subgroup : Subgroup GroupType)
    (invariant : ∀ actorElement : ActorType, ∀ element ∈ subgroup,
      actorElement • element ∈ subgroup)
    (element : GroupType) (fixed : ∀ actorElement : ActorType, actorElement • element = element) :
    ∀ actorElement : ActorType, ∀ representative ∈ conjugateSubgroup element subgroup,
      actorElement • representative ∈ conjugateSubgroup element subgroup := by
  intro actorElement representative member
  obtain ⟨original, original_member, rfl⟩ := member
  refine ⟨actorElement • original, invariant actorElement original original_member, ?_⟩
  change element * (actorElement • original) * element⁻¹ =
    actorElement • (element * original * element⁻¹)
  rw [MulDistribMulAction.smul_mul, MulDistribMulAction.smul_mul, smul_inv', fixed]

theorem invariant_hall_intersection_invariant (primes : Set ℕ) :
    ∀ actorElement : ActorType,
      ∀ element ∈ invariantHallIntersection (ActorType := ActorType) (GroupType := GroupType) primes,
        actorElement • element ∈ invariantHallIntersection (ActorType := ActorType)
          (GroupType := GroupType) primes := by
  intro actorElement element member
  apply Subgroup.mem_iInf.mpr
  intro hall
  apply Subgroup.mem_iInf.mpr
  intro property
  exact property.2 actorElement element (invariant_hall_intersection_le primes hall property.1
    property.2 member)

theorem invariant_hall_intersection_fixed_normalized (primes : Set ℕ) :
    FixedPoints.subgroup ActorType GroupType ≤ Subgroup.normalizer
      (invariantHallIntersection (ActorType := ActorType) (GroupType := GroupType) primes :
        Set GroupType) := by
  apply Subgroup.le_normalizer_iff.mpr
  intro element fixed representative member
  apply Subgroup.mem_iInf.mpr
  intro hall
  apply Subgroup.mem_iInf.mpr
  intro property
  have inverse_fixed : ∀ actorElement : ActorType, actorElement • element⁻¹ = element⁻¹ := by
    intro actorElement
    rw [smul_inv', fixed actorElement]
  have inverseHall_invariant := invariant_conjugate_of_fixed hall property.2 element⁻¹ inverse_fixed
  have member_inverseHall := invariant_hall_intersection_le primes
    (conjugateSubgroup element⁻¹ hall) (hall_conjugate primes hall element⁻¹ property.1)
    inverseHall_invariant member
  have mapped := Subgroup.mem_map_of_mem (MulAut.conj element).toMonoidHom member_inverseHall
  change element * representative * element⁻¹ ∈
    conjugateSubgroup element (conjugateSubgroup element⁻¹ hall) at mapped
  rwa [conjugate_subgroup_mul, mul_inv_cancel, conjugate_subgroup_one] at mapped

theorem fixed_normalized_prime_hull_eq_invariant_hall_intersection
    [Finite ActorType] [Finite GroupType] [Group.IsSolvable GroupType]
    (prime : ℕ) (prime_prime : prime.Prime) (actor_pgroup : IsPGroup prime ActorType)
    (coprime : Nat.Coprime prime (Nat.card GroupType)) (primes : Set ℕ) :
    fixedNormalizedPrimeHull (ActorType := ActorType) (GroupType := GroupType) primes =
      invariantHallIntersection (ActorType := ActorType) (GroupType := GroupType) primes := by
  apply le_antisymm
  · apply le_iInf
    intro hall
    apply le_iInf
    intro property
    apply iSup_le
    intro subgroup
    apply iSup_le
    intro candidate
    exact fixed_normalized_prime_subgroup_le_invariant_hall prime prime_prime actor_pgroup coprime
      primes subgroup hall candidate.1 candidate.2.1 candidate.2.2 property.1 property.2
  · obtain ⟨hall, _, hall_property, hall_invariant⟩ := invariant_hall_subgroup_containing prime
      prime_prime ActorType actor_pgroup GroupType coprime primes ⊥
      (by rw [Subgroup.card_bot]; exact prime_supported_one primes)
      (by intro actorElement element member; rw [Subgroup.mem_bot.mp member, smul_one];
          exact Subgroup.one_mem _)
    exact fixed_normalized_prime_hull_contains primes _
      (prime_supported_of_dvd primes hall_property.1 (Subgroup.card_dvd_of_le
        (invariant_hall_intersection_le primes hall hall_property hall_invariant)))
      (invariant_hall_intersection_invariant primes)
      (invariant_hall_intersection_fixed_normalized primes)

end CFSG.SignalizerFunctor.Helpers
