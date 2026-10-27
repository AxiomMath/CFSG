module

public import CFSG.LocalAnalysis.SignalizerFunctor.NormalizedHallIntersections
public import CFSG.LocalAnalysis.SignalizerFunctor.InvariantHallIntersection

public section

universe actorUniverse groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {ActorType : Type actorUniverse} [Group ActorType] [Finite ActorType]
variable {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]
variable [Group.IsSolvable GroupType] [MulDistribMulAction ActorType GroupType]

theorem invariant_hall_intersection_restriction
    (prime : ℕ) (prime_prime : prime.Prime) (actor_pgroup : IsPGroup prime ActorType)
    (coprime : Nat.Coprime prime (Nat.card GroupType)) (primes : Set ℕ)
    (target : Subgroup GroupType)
    (invariant : ∀ actorElement : ActorType, ∀ element ∈ target, actorElement • element ∈ target)
    (fixed_normalized : FixedPoints.subgroup ActorType GroupType ≤
      Subgroup.normalizer (target : Set GroupType)) :
    let _action := invariantSubgroupAction target invariant
    (invariantHallIntersection (ActorType := ActorType) (GroupType := target) primes).map
      target.subtype = invariantHallIntersection (ActorType := ActorType)
        (GroupType := GroupType) primes ⊓ target := by
  let _action := invariantSubgroupAction target invariant
  change (invariantHallIntersection (ActorType := ActorType) (GroupType := target) primes).map
    target.subtype = invariantHallIntersection (ActorType := ActorType)
      (GroupType := GroupType) primes ⊓ target
  apply le_antisymm
  · refine le_inf ?_ (Subgroup.map_subtype_le _)
    apply le_iInf
    intro hall
    apply le_iInf
    intro property
    have restricted_hall := invariant_hall_normalized_intersection prime prime_prime ActorType
      actor_pgroup coprime primes hall target property.1 property.2 invariant fixed_normalized
    have restricted_invariant : ∀ actorElement : ActorType, ∀ element ∈ hall.subgroupOf target,
        actorElement • element ∈ hall.subgroupOf target := by
      intro actorElement element member
      exact property.2 actorElement element.val member
    exact (Subgroup.map_mono (invariant_hall_intersection_le primes (hall.subgroupOf target)
      restricted_hall.1 restricted_invariant)).trans
        (by rw [Subgroup.subgroupOf_map_subtype]; exact inf_le_left)
  · intro element member
    refine ⟨⟨element, member.2⟩, ?_, rfl⟩
    apply Subgroup.mem_iInf.mpr
    intro internalHall
    apply Subgroup.mem_iInf.mpr
    intro property
    let embedded := internalHall.map target.subtype
    have embedded_supported : primeSupported primes (Nat.card embedded) := by
      rw [Subgroup.card_map_of_injective target.subtype_injective]
      exact property.1.1
    have embedded_invariant : ∀ actorElement : ActorType, ∀ representative ∈ embedded,
        actorElement • representative ∈ embedded := by
      intro actorElement representative representative_member
      obtain ⟨original, original_member, rfl⟩ := representative_member
      exact ⟨actorElement • original, property.2 actorElement original original_member, rfl⟩
    obtain ⟨hall, contains_embedded, hall_property, hall_invariant⟩ :=
      invariant_hall_subgroup_containing prime prime_prime ActorType actor_pgroup GroupType coprime
        primes embedded embedded_supported embedded_invariant
    have embedded_internal : embedded.subgroupOf target = internalHall :=
      Subgroup.comap_map_eq_self_of_injective target.subtype_injective _
    have intersection_equal : hall.subgroupOf target = internalHall := by
      apply hall_supported_overgroup_eq primes internalHall (hall.subgroupOf target) property.1
      · rw [← embedded_internal]
        exact Subgroup.subgroupOf_mono target contains_embedded
      · exact prime_supported_of_dvd primes hall_property.1
          (Subgroup.card_comap_dvd_of_injective hall target.subtype target.subtype_injective)
    rw [← intersection_equal]
    exact invariant_hall_intersection_le primes hall hall_property hall_invariant member.1

theorem fixed_normalized_prime_hull_restriction
    (prime : ℕ) (prime_prime : prime.Prime) (actor_pgroup : IsPGroup prime ActorType)
    (coprime : Nat.Coprime prime (Nat.card GroupType)) (primes : Set ℕ)
    (target : Subgroup GroupType)
    (invariant : ∀ actorElement : ActorType, ∀ element ∈ target, actorElement • element ∈ target)
    (fixed_normalized : FixedPoints.subgroup ActorType GroupType ≤
      Subgroup.normalizer (target : Set GroupType)) :
    let _action := invariantSubgroupAction target invariant
    (fixedNormalizedPrimeHull (ActorType := ActorType) (GroupType := target) primes).map
      target.subtype = fixedNormalizedPrimeHull (ActorType := ActorType)
        (GroupType := GroupType) primes ⊓ target := by
  let _action := invariantSubgroupAction target invariant
  change (fixedNormalizedPrimeHull (ActorType := ActorType) (GroupType := target) primes).map
    target.subtype = fixedNormalizedPrimeHull (ActorType := ActorType)
      (GroupType := GroupType) primes ⊓ target
  have target_coprime : Nat.Coprime prime (Nat.card target) :=
    coprime.of_dvd_right (Subgroup.card_subgroup_dvd_card target)
  rw [fixed_normalized_prime_hull_eq_invariant_hall_intersection prime prime_prime actor_pgroup
    target_coprime primes,
    fixed_normalized_prime_hull_eq_invariant_hall_intersection prime prime_prime actor_pgroup
      coprime primes]
  exact invariant_hall_intersection_restriction prime prime_prime actor_pgroup coprime primes
    target invariant fixed_normalized

end CFSG.SignalizerFunctor.Helpers
