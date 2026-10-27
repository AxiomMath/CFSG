module

public import CFSG.LocalAnalysis.SignalizerFunctor.SemidirectHall
public import CFSG.LocalAnalysis.SignalizerFunctor.InvariantHallConjugacy

public section

universe actorUniverse groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

open scoped Pointwise

variable {GroupType : Type groupUniverse} [Group GroupType]

theorem hall_supported_overgroup_eq (primes : Set ℕ) (hall candidate : Subgroup GroupType)
    (hall_property : IsHallSubgroup primes hall) (contained : hall ≤ candidate)
    (supported : primeSupported primes (Nat.card candidate)) : candidate = hall := by
  have internal_hall := hall_subgroupOf primes hall candidate contained hall_property
  have internal_top := hall_eq_top_of_group_supported primes (hall.subgroupOf candidate)
    internal_hall supported
  have mapped := congrArg (Subgroup.map candidate.subtype) internal_top
  rw [Subgroup.map_subgroupOf_eq_of_le contained, ← MonoidHom.range_eq_map,
    candidate.subtype_range] at mapped
  exact mapped.symm

theorem hall_conjugate_subgroupOf (primes : Set ℕ) (parent subgroup : Subgroup GroupType)
    (element : GroupType) (normalized : element ∈ Subgroup.normalizer (parent : Set GroupType))
    (hall : IsHallSubgroup primes (subgroup.subgroupOf parent)) :
    IsHallSubgroup primes ((conjugateSubgroup element subgroup).subgroupOf parent) := by
  have parent_preserved : conjugateSubgroup element parent = parent :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp normalized
  have intersection_equal : conjugateSubgroup element (subgroup ⊓ parent) =
      conjugateSubgroup element subgroup ⊓ parent := by
    change (subgroup ⊓ parent).map (MulAut.conj element).toMonoidHom = _
    rw [Subgroup.map_inf _ _ _ (MulAut.conj element).injective]
    exact congrArg (fun candidate => conjugateSubgroup element subgroup ⊓ candidate) parent_preserved
  constructor
  · have cardinality : Nat.card ((conjugateSubgroup element subgroup).subgroupOf parent) =
        Nat.card (subgroup.subgroupOf parent) := by
      rw [← Subgroup.card_map_of_injective parent.subtype_injective,
        Subgroup.subgroupOf_map_subtype, ← intersection_equal, conjugate_subgroup_card,
        ← Subgroup.subgroupOf_map_subtype,
        Subgroup.card_map_of_injective parent.subtype_injective]
    rw [cardinality]
    exact hall.1
  · have index_equal := Subgroup.relIndex_pointwise_smul (MulAut.conj element) subgroup parent
    change (conjugateSubgroup element subgroup).relIndex (conjugateSubgroup element parent) =
      subgroup.relIndex parent at index_equal
    rw [parent_preserved] at index_equal
    change primeSupported primesᶜ ((conjugateSubgroup element subgroup).relIndex parent)
    rw [index_equal]
    exact hall.2

theorem invariant_hall_normalized_intersection
    (prime : ℕ) (prime_prime : prime.Prime)
    (ActorType : Type actorUniverse) [Group ActorType] [Finite ActorType]
    (actor_pgroup : IsPGroup prime ActorType)
    [Finite GroupType] [Group.IsSolvable GroupType] [MulDistribMulAction ActorType GroupType]
    (coprime : Nat.Coprime prime (Nat.card GroupType))
    (primes : Set ℕ) (hall target : Subgroup GroupType)
    (hall_property : IsHallSubgroup primes hall)
    (hall_invariant : ∀ actorElement : ActorType, ∀ element ∈ hall,
      actorElement • element ∈ hall)
    (target_invariant : ∀ actorElement : ActorType, ∀ element ∈ target,
      actorElement • element ∈ target)
    (fixed_normalized : FixedPoints.subgroup ActorType GroupType ≤
      Subgroup.normalizer (target : Set GroupType)) :
    IsHallSubgroup primes (hall.subgroupOf target) ∧
      (∀ actorElement : ActorType, ∀ element ∈ hall ⊓ target,
        actorElement • element ∈ hall ⊓ target) := by
  let _targetAction := invariantSubgroupAction target target_invariant
  have target_coprime : Nat.Coprime prime (Nat.card target) :=
    coprime.of_dvd_right (Subgroup.card_subgroup_dvd_card target)
  have internal_supported : primeSupported primes (Nat.card (hall.subgroupOf target)) :=
    prime_supported_of_dvd primes hall_property.1
      (Subgroup.card_comap_dvd_of_injective hall target.subtype target.subtype_injective)
  have internal_invariant : ∀ actorElement : ActorType, ∀ element ∈ hall.subgroupOf target,
      actorElement • element ∈ hall.subgroupOf target := by
    intro actorElement element member
    exact hall_invariant actorElement element.val member
  obtain ⟨internalHall, contains_intersection, internal_hall, internal_hall_invariant⟩ :=
    invariant_hall_subgroup_containing prime prime_prime ActorType actor_pgroup target target_coprime
      primes (hall.subgroupOf target) internal_supported internal_invariant
  let embedded := internalHall.map target.subtype
  have embedded_supported : primeSupported primes (Nat.card embedded) := by
    rw [Subgroup.card_map_of_injective target.subtype_injective]
    exact internal_hall.1
  have embedded_invariant : ∀ actorElement : ActorType, ∀ element ∈ embedded,
      actorElement • element ∈ embedded := by
    intro actorElement element member
    obtain ⟨representative, representative_member, rfl⟩ := member
    exact ⟨actorElement • representative, internal_hall_invariant actorElement representative
      representative_member, rfl⟩
  obtain ⟨otherHall, embedded_contained, other_hall, other_invariant⟩ :=
    invariant_hall_subgroup_containing prime prime_prime ActorType actor_pgroup GroupType coprime
      primes embedded embedded_supported embedded_invariant
  have internal_image : embedded.subgroupOf target = internalHall :=
    Subgroup.comap_map_eq_self_of_injective target.subtype_injective _
  have other_intersection : otherHall.subgroupOf target = internalHall := by
    apply hall_supported_overgroup_eq primes internalHall (otherHall.subgroupOf target)
      internal_hall
    · rw [← internal_image]
      exact Subgroup.subgroupOf_mono target embedded_contained
    · exact prime_supported_of_dvd primes other_hall.1
        (Subgroup.card_comap_dvd_of_injective otherHall target.subtype target.subtype_injective)
  obtain ⟨element, conjugates, fixed⟩ := invariant_hall_subgroups_conjugate_by_fixed_element prime
    prime_prime ActorType actor_pgroup GroupType coprime primes otherHall hall other_hall hall_property
    other_invariant hall_invariant
  have other_intersection_hall : IsHallSubgroup primes (otherHall.subgroupOf target) := by
    rw [other_intersection]
    exact internal_hall
  have conjugate_hall := hall_conjugate_subgroupOf primes target otherHall element
    (fixed_normalized fixed) other_intersection_hall
  rw [conjugates] at conjugate_hall
  exact ⟨conjugate_hall, fun actorElement _ member =>
    ⟨hall_invariant actorElement _ member.1, target_invariant actorElement _ member.2⟩⟩

end CFSG.SignalizerFunctor.Helpers
