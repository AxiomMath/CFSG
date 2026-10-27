module

public import CFSG.LocalAnalysis.SignalizerFunctor.NormalizedSylowIntersections

public section

universe actorUniverse groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {ActorType : Type actorUniverse} [Group ActorType]
variable {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]
variable [MulDistribMulAction ActorType GroupType]

omit [Finite GroupType] in
theorem invariant_inf_subgroups (first second : Subgroup GroupType)
    (first_invariant : ∀ actorElement : ActorType, ∀ element ∈ first, actorElement • element ∈ first)
    (second_invariant : ∀ actorElement : ActorType, ∀ element ∈ second, actorElement • element ∈ second) :
    ∀ actorElement : ActorType, ∀ element ∈ first ⊓ second, actorElement • element ∈ first ⊓ second := by
  intro actorElement element member
  exact ⟨first_invariant actorElement element member.1, second_invariant actorElement element member.2⟩

omit [Finite GroupType] in
theorem full_fixed_normalizes_subgroup_fixed (actorSubgroup : Subgroup ActorType) :
    FixedPoints.subgroup ActorType GroupType ≤
      Subgroup.normalizer (FixedPoints.subgroup actorSubgroup GroupType : Set GroupType) := by
  apply Subgroup.le_normalizer_iff.mpr
  intro conjugator fixed element member actorElement
  change actorElement.val • (conjugator * element * conjugator⁻¹) = conjugator * element * conjugator⁻¹
  have element_fixed : actorElement.val • element = element := member actorElement
  rw [MulDistribMulAction.smul_mul, MulDistribMulAction.smul_mul, smul_inv',
    fixed actorElement.val, element_fixed]

theorem fixed_normalized_sylow_intersection_card
    (prime groupPrime : ℕ) (prime_prime : prime.Prime) (groupPrime_prime : groupPrime.Prime)
    (actor_pgroup : IsPGroup prime ActorType) (coprime : Nat.Coprime prime (Nat.card GroupType))
    (sylow : Sylow groupPrime GroupType)
    (fixed : ∀ actorElement : ActorType, actorElement • sylow = sylow)
    (subgroup : Subgroup GroupType)
    (invariant : ∀ actorElement : ActorType, ∀ element ∈ subgroup, actorElement • element ∈ subgroup)
    (fixed_normalized : FixedPoints.subgroup ActorType GroupType ≤
      Subgroup.normalizer (subgroup : Set GroupType)) :
    Nat.card ((sylow : Subgroup GroupType) ⊓ subgroup : Subgroup GroupType) =
      groupPrime ^ (Nat.card subgroup).factorization groupPrime := by
  obtain ⟨internalSylow, image_eq, _⟩ := fixed_normalized_invariant_sylow_intersection prime groupPrime
    prime_prime groupPrime_prime actor_pgroup coprime sylow fixed subgroup invariant fixed_normalized
  rw [← image_eq, Subgroup.card_map_of_injective subgroup.subtype_injective]
  let : Fact groupPrime.Prime := ⟨groupPrime_prime⟩
  exact internalSylow.card_eq_multiplicity

theorem invariant_sylow_with_supplement_intersection_parts
    (prime groupPrime : ℕ) (prime_prime : prime.Prime) (groupPrime_prime : groupPrime.Prime)
    (actor_pgroup : IsPGroup prime ActorType) (coprime : Nat.Coprime prime (Nat.card GroupType))
    (supplement : Subgroup GroupType)
    (supplement_invariant : ∀ actorElement : ActorType, ∀ element ∈ supplement,
      actorElement • element ∈ supplement) :
    ∃ sylow : Sylow groupPrime GroupType,
      (∀ actorElement : ActorType, actorElement • sylow = sylow) ∧
      Nat.card ((sylow : Subgroup GroupType) ⊓ supplement : Subgroup GroupType) =
        groupPrime ^ (Nat.card supplement).factorization groupPrime ∧
      ∀ subgroup : Subgroup GroupType,
        (∀ actorElement : ActorType, ∀ element ∈ subgroup, actorElement • element ∈ subgroup) →
        FixedPoints.subgroup ActorType GroupType ≤ Subgroup.normalizer (subgroup : Set GroupType) →
        Nat.card ((sylow : Subgroup GroupType) ⊓ subgroup : Subgroup GroupType) =
          groupPrime ^ (Nat.card subgroup).factorization groupPrime ∧
        Nat.card (((sylow : Subgroup GroupType) ⊓ supplement) ⊓ subgroup : Subgroup GroupType) =
          groupPrime ^ (Nat.card (supplement ⊓ subgroup : Subgroup GroupType)).factorization groupPrime := by
  let : Fact groupPrime.Prime := ⟨groupPrime_prime⟩
  let _supplementAction := invariantSubgroupAction supplement supplement_invariant
  have supplement_coprime := coprime.of_dvd_right supplement.card_subgroup_dvd_card
  obtain ⟨internalSylow, internal_fixed⟩ := invariant_sylow_exists prime groupPrime prime_prime
    groupPrime_prime actor_pgroup supplement_coprime
  let embedded := (internalSylow : Subgroup supplement).map supplement.subtype
  have embedded_invariant : ∀ actorElement : ActorType, ∀ element ∈ embedded,
      actorElement • element ∈ embedded := by
    rintro actorElement element ⟨original, member, rfl⟩
    exact Subgroup.mem_map_of_mem supplement.subtype
      ((invariant_sylow_subgroup_iff groupPrime internalSylow).mp internal_fixed actorElement original member)
  obtain ⟨sylow, contains, fixed⟩ := invariant_sylow_containing prime groupPrime prime_prime
    groupPrime_prime actor_pgroup coprime embedded (internalSylow.isPGroup'.map supplement.subtype)
    embedded_invariant
  have intersection_eq : (sylow : Subgroup GroupType) ⊓ supplement = embedded := by
    have internal_contains : (internalSylow : Subgroup supplement) ≤
        (sylow : Subgroup GroupType).subgroupOf supplement := by
      intro element member
      exact contains (Subgroup.mem_map_of_mem supplement.subtype member)
    have internal_pgroup : IsPGroup groupPrime ((sylow : Subgroup GroupType).subgroupOf supplement) :=
      (sylow.isPGroup'.to_le
        (show (sylow : Subgroup GroupType) ⊓ supplement ≤ sylow from inf_le_left)).of_equiv
        ((Subgroup.subgroupOfEquivOfLe
          (show (sylow : Subgroup GroupType) ⊓ supplement ≤ supplement from inf_le_right)).symm.trans
          (MulEquiv.subgroupCongr (show ((sylow : Subgroup GroupType) ⊓ supplement).subgroupOf supplement =
            (sylow : Subgroup GroupType).subgroupOf supplement from by
              ext element
              exact and_iff_left element.property)))
    have maximal := internalSylow.is_maximal' internal_pgroup internal_contains
    have image_eq := congrArg (Subgroup.map supplement.subtype) maximal
    rw [Subgroup.subgroupOf_map_subtype] at image_eq
    exact image_eq
  refine ⟨sylow, fixed, ?_, ?_⟩
  · rw [intersection_eq, Subgroup.card_map_of_injective supplement.subtype_injective]
    exact internalSylow.card_eq_multiplicity
  · intro subgroup invariant normalized
    refine ⟨fixed_normalized_sylow_intersection_card prime groupPrime prime_prime groupPrime_prime
      actor_pgroup coprime sylow fixed subgroup invariant normalized, ?_⟩
    have internal_invariant : ∀ actorElement : ActorType, ∀ element ∈ subgroup.subgroupOf supplement,
        actorElement • element ∈ subgroup.subgroupOf supplement := by
      intro actorElement element member
      exact invariant actorElement element.val member
    have internal_normalized : FixedPoints.subgroup ActorType supplement ≤
        Subgroup.normalizer (subgroup.subgroupOf supplement : Set supplement) := by
      apply Subgroup.le_normalizer_iff.mpr
      intro conjugator fixed element member
      have ambient_fixed : conjugator.val ∈ FixedPoints.subgroup ActorType GroupType := by
        intro actorElement
        exact congrArg Subtype.val (fixed actorElement)
      exact Subgroup.le_normalizer_iff.mp normalized conjugator.val ambient_fixed element.val member
    have internal_card := fixed_normalized_sylow_intersection_card prime groupPrime prime_prime groupPrime_prime
      actor_pgroup supplement_coprime internalSylow internal_fixed (subgroup.subgroupOf supplement)
      internal_invariant internal_normalized
    have mapped_intersection :
        ((internalSylow : Subgroup supplement) ⊓ subgroup.subgroupOf supplement).map supplement.subtype =
          ((sylow : Subgroup GroupType) ⊓ supplement) ⊓ subgroup := by
      rw [Subgroup.map_inf _ _ _ supplement.subtype_injective, Subgroup.subgroupOf_map_subtype]
      change embedded ⊓ (subgroup ⊓ supplement) = _
      rw [← intersection_eq]
      ext element
      constructor
      · exact fun member => ⟨member.1, member.2.1⟩
      · exact fun member => ⟨member.1, member.2, member.1.2⟩
    rw [← Subgroup.card_map_of_injective supplement.subtype_injective,
      mapped_intersection] at internal_card
    have internal_subgroup_card : Nat.card (subgroup.subgroupOf supplement) =
        Nat.card (supplement ⊓ subgroup : Subgroup GroupType) := by
      rw [← Subgroup.card_map_of_injective supplement.subtype_injective,
        Subgroup.subgroupOf_map_subtype, inf_comm]
    rwa [internal_subgroup_card] at internal_card

end CFSG.SignalizerFunctor.Helpers
