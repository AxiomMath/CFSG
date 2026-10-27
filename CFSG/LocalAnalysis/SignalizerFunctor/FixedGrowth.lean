module

public import CFSG.LocalAnalysis.SignalizerFunctor.ElementaryGeneration
public import CFSG.LocalAnalysis.SignalizerFunctor.InvariantSylowContainment

public section

universe actorUniverse groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

theorem cyclic_quotient_pair_intersection_card_bound
    (prime rank : ℕ) (prime_prime : prime.Prime)
    (ActorType : Type actorUniverse) [CommGroup ActorType] [Finite ActorType]
    (exponent : ∀ element : ActorType, element ^ prime = 1)
    (large : prime ^ (rank + 2) ≤ Nat.card ActorType)
    (first second : Subgroup ActorType)
    (first_cyclic : IsCyclic (ActorType ⧸ first))
    (second_cyclic : IsCyclic (ActorType ⧸ second)) :
    prime ^ rank ≤ Nat.card (first ⊓ second : Subgroup ActorType) := by
  have first_index := cyclic_quotient_index_le_prime prime prime_prime ActorType
    exponent first first_cyclic
  have second_index := cyclic_quotient_index_le_prime prime prime_prime ActorType
    exponent second second_cyclic
  have intersection_index := (Subgroup.index_inf_le (H := first) (K := second)).trans
    (Nat.mul_le_mul first_index second_index)
  have cardinality := (first ⊓ second).card_mul_index
  have product_bound := Nat.mul_le_mul_left
    (Nat.card (first ⊓ second : Subgroup ActorType)) intersection_index
  rw [cardinality] at product_bound
  rw [pow_add, pow_two] at large
  exact Nat.le_of_mul_le_mul_right (large.trans product_bound)
    (Nat.mul_pos prime_prime.pos prime_prime.pos)

theorem cyclic_quotient_pair_intersection_nontrivial
    (prime : ℕ) (prime_prime : prime.Prime)
    (ActorType : Type actorUniverse) [CommGroup ActorType] [Finite ActorType]
    (exponent : ∀ element : ActorType, element ^ prime = 1)
    (large : prime ^ 3 ≤ Nat.card ActorType)
    (first second : Subgroup ActorType)
    (first_cyclic : IsCyclic (ActorType ⧸ first))
    (second_cyclic : IsCyclic (ActorType ⧸ second)) :
    ∃ element : ActorType, element ≠ 1 ∧ element ∈ first ∧ element ∈ second := by
  have first_index := cyclic_quotient_index_le_prime prime prime_prime ActorType
    exponent first first_cyclic
  have second_index := cyclic_quotient_index_le_prime prime prime_prime ActorType
    exponent second second_cyclic
  have intersection_nontrivial : first ⊓ second ≠ ⊥ := by
    intro trivial
    have index_bound := Subgroup.index_inf_le (H := first) (K := second)
    rw [trivial, Subgroup.index_bot] at index_bound
    have product_bound := Nat.mul_le_mul first_index second_index
    have cube : prime ^ 3 = prime * prime * prime := by ring
    rw [cube] at large
    nlinarith [prime_prime.two_le]
  obtain ⟨element, nonidentity⟩ :=
    Subgroup.ne_bot_iff_exists_ne_one.mp intersection_nontrivial
  refine ⟨element.val, ?_, element.property.1, element.property.2⟩
  intro identity
  apply nonidentity
  exact Subtype.ext identity

variable {GroupType : Type groupUniverse} [Group GroupType]

theorem exists_cyclic_quotient_fixed_points_escape
    (ActorType : Type actorUniverse) [CommGroup ActorType] [Finite ActorType]
    [Finite GroupType] [MulDistribMulAction ActorType GroupType]
    (prime : ℕ) (prime_prime : prime.Prime)
    (actor_pgroup : IsPGroup prime ActorType)
    (target bound : Subgroup GroupType)
    (invariant : ∀ actorElement : ActorType, ∀ element ∈ target,
      actorElement • element ∈ target)
    (coprime : Nat.Coprime prime (Nat.card target))
    (not_contained : ¬ target ≤ bound) :
    ∃ actorSubgroup : Subgroup ActorType, IsCyclic (ActorType ⧸ actorSubgroup) ∧
      ¬ target ⊓ FixedPoints.subgroup actorSubgroup GroupType ≤ bound := by
  classical
  let _targetAction := invariantSubgroupAction target invariant
  have generated := coprime_cyclic_quotient_generation prime prime_prime ActorType
    actor_pgroup target coprime
  have target_generated :
      (⨆ (actorSubgroup : Subgroup ActorType)
        (_ : IsCyclic (ActorType ⧸ actorSubgroup)),
        FixedPoints.subgroup actorSubgroup target).map target.subtype = target := by
    rw [generated, ← MonoidHom.range_eq_map, target.subtype_range]
  by_contra! all_contained
  apply not_contained
  conv_lhs => rw [← target_generated]
  rw [Subgroup.map_iSup]
  apply iSup_le
  intro actorSubgroup
  rw [Subgroup.map_iSup]
  apply iSup_le
  intro cyclic
  apply le_trans _ (all_contained actorSubgroup cyclic)
  rintro element ⟨representative, fixed, rfl⟩
  refine ⟨representative.property, ?_⟩
  intro actorElement
  exact congrArg (fun internal : target => (internal : GroupType)) (fixed actorElement)

theorem invariant_subgroups_pair_fixed_growth
    (ActorType : Type actorUniverse) [CommGroup ActorType] [Finite ActorType]
    [Finite GroupType] [MulDistribMulAction ActorType GroupType]
    (prime rank : ℕ) (prime_prime : prime.Prime)
    (exponent : ∀ element : ActorType, element ^ prime = 1)
    (large : prime ^ (rank + 2) ≤ Nat.card ActorType)
    (first second bound : Subgroup GroupType)
    (first_invariant : ∀ actorElement : ActorType, ∀ element ∈ first,
      actorElement • element ∈ first)
    (second_invariant : ∀ actorElement : ActorType, ∀ element ∈ second,
      actorElement • element ∈ second)
    (first_coprime : Nat.Coprime prime (Nat.card first))
    (second_coprime : Nat.Coprime prime (Nat.card second))
    (first_escape : ¬ first ≤ bound) (second_escape : ¬ second ≤ bound) :
    ∃ actorSubgroup : Subgroup ActorType, Nat.card actorSubgroup = prime ^ rank ∧
      ¬ first ⊓ FixedPoints.subgroup actorSubgroup GroupType ≤ bound ∧
      ¬ second ⊓ FixedPoints.subgroup actorSubgroup GroupType ≤ bound := by
  have actor_pgroup : IsPGroup prime ActorType := by
    intro element
    exact ⟨1, by simpa using exponent element⟩
  obtain ⟨firstKernel, first_cyclic, first_fixed_escape⟩ :=
    exists_cyclic_quotient_fixed_points_escape ActorType prime prime_prime actor_pgroup
      first bound first_invariant first_coprime first_escape
  obtain ⟨secondKernel, second_cyclic, second_fixed_escape⟩ :=
    exists_cyclic_quotient_fixed_points_escape ActorType prime prime_prime actor_pgroup
      second bound second_invariant second_coprime second_escape
  have intersection_large := cyclic_quotient_pair_intersection_card_bound prime rank
    prime_prime ActorType exponent large firstKernel secondKernel first_cyclic second_cyclic
  obtain ⟨internal, internal_card⟩ := Sylow.exists_subgroup_card_pow_prime_of_le_card
    prime_prime (actor_pgroup.to_subgroup (firstKernel ⊓ secondKernel)) intersection_large
  let actorSubgroup := internal.map (firstKernel ⊓ secondKernel).subtype
  have contained : actorSubgroup ≤ firstKernel ⊓ secondKernel := by
    rintro element ⟨representative, _, rfl⟩
    exact representative.property
  have first_fixed_le : FixedPoints.subgroup firstKernel GroupType ≤
      FixedPoints.subgroup actorSubgroup GroupType := by
    intro element fixed actorElement
    exact fixed ⟨actorElement.val, (contained actorElement.property).1⟩
  have second_fixed_le : FixedPoints.subgroup secondKernel GroupType ≤
      FixedPoints.subgroup actorSubgroup GroupType := by
    intro element fixed actorElement
    exact fixed ⟨actorElement.val, (contained actorElement.property).2⟩
  refine ⟨actorSubgroup, ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective (firstKernel ⊓ secondKernel).subtype_injective]
    exact internal_card
  · intro contained_fixed
    exact first_fixed_escape ((inf_le_inf_left first first_fixed_le).trans contained_fixed)
  · intro contained_fixed
    exact second_fixed_escape ((inf_le_inf_left second second_fixed_le).trans contained_fixed)

theorem normalizer_subgroupOf_map (target bound : Subgroup GroupType)
    (contained : bound ≤ target) :
    (Subgroup.normalizer (bound.subgroupOf target : Set target)).map target.subtype =
      target ⊓ Subgroup.normalizer (bound : Set GroupType) := by
  ext element
  constructor
  · rintro ⟨representative, normalizes, rfl⟩
    refine ⟨representative.property, Subgroup.mem_normalizer_iff.mpr ?_⟩
    intro boundElement
    constructor
    · intro member
      have internal := (Subgroup.mem_normalizer_iff.mp normalizes
        (⟨boundElement, contained member⟩ : target)).mp member
      exact internal
    · intro member
      have target_member : boundElement ∈ target := by
        have member_conjugate := contained member
        have member_original := target.mul_mem
          (target.mul_mem (target.inv_mem representative.property) member_conjugate)
          representative.property
        change representative.val⁻¹ *
          (representative.val * boundElement * representative.val⁻¹) *
          representative.val ∈ target at member_original
        have identity : representative.val⁻¹ *
            (representative.val * boundElement * representative.val⁻¹) *
            representative.val = boundElement := by group
        rwa [identity] at member_original
      exact (Subgroup.mem_normalizer_iff.mp normalizes
        (⟨boundElement, target_member⟩ : target)).mpr member
  · rintro ⟨member, normalizes⟩
    refine ⟨⟨element, member⟩, Subgroup.mem_normalizer_iff.mpr ?_, rfl⟩
    intro boundElement
    exact Subgroup.mem_normalizer_iff.mp normalizes boundElement.val

theorem pgroup_normalizer_strict_growth [Finite GroupType]
    (prime : ℕ) (prime_prime : prime.Prime)
    (target bound : Subgroup GroupType) (target_pgroup : IsPGroup prime target)
    (proper : bound < target) :
    bound < target ⊓ Subgroup.normalizer (bound : Set GroupType) := by
  let : Fact prime.Prime := ⟨prime_prime⟩
  let _nilpotent : Group.IsNilpotent target := target_pgroup.isNilpotent
  have internal_proper : bound.subgroupOf target < ⊤ := by
    apply lt_top_iff_ne_top.mpr
    intro equality
    exact proper.not_ge (Subgroup.subgroupOf_eq_top.mp equality)
  have growth := Group.normalizerCondition_of_isNilpotent
    (bound.subgroupOf target) internal_proper
  refine lt_iff_le_not_ge.mpr ⟨le_inf proper.le Subgroup.le_normalizer, ?_⟩
  intro no_growth
  apply growth.not_ge
  intro element normalizes
  have image_member := Subgroup.mem_map_of_mem target.subtype normalizes
  rw [normalizer_subgroupOf_map target bound proper.le] at image_member
  exact no_growth image_member

theorem prime_coprime_pgroup_card [Finite GroupType]
    (prime groupPrime : ℕ) (prime_prime : prime.Prime)
    (groupPrime_prime : groupPrime.Prime) (distinct : prime ≠ groupPrime)
    (pgroup : IsPGroup groupPrime GroupType) :
    Nat.Coprime prime (Nat.card GroupType) := by
  let : Fact groupPrime.Prime := ⟨groupPrime_prime⟩
  obtain ⟨rank, cardinality⟩ := IsPGroup.iff_card.mp pgroup
  rw [cardinality]
  apply groupPrime_prime.coprime_pow_of_not_dvd
  intro divides
  exact distinct ((prime_prime.dvd_iff_eq groupPrime_prime.ne_one).mp divides)

theorem pairwise_normalizer_fixed_growth
    (ActorType : Type actorUniverse) [CommGroup ActorType] [Finite ActorType]
    [Finite GroupType] [MulDistribMulAction ActorType GroupType]
    (prime groupPrime : ℕ) (prime_prime : prime.Prime)
    (groupPrime_prime : groupPrime.Prime) (distinct : prime ≠ groupPrime)
    (exponent : ∀ element : ActorType, element ^ prime = 1)
    (large : prime ^ 3 ≤ Nat.card ActorType)
    (first second : Subgroup GroupType)
    (first_pgroup : IsPGroup groupPrime first)
    (second_pgroup : IsPGroup groupPrime second)
    (first_invariant : ∀ actorElement : ActorType, ∀ element ∈ first,
      actorElement • element ∈ first)
    (second_invariant : ∀ actorElement : ActorType, ∀ element ∈ second,
      actorElement • element ∈ second)
    (first_proper : first ⊓ second < first)
    (second_proper : first ⊓ second < second) :
    ∃ actorElement : ActorType, actorElement ≠ 1 ∧
      (∃ element ∈ first ⊓ Subgroup.normalizer (first ⊓ second : Set GroupType),
        element ∉ first ⊓ second ∧ actorElement • element = element) ∧
      (∃ element ∈ second ⊓ Subgroup.normalizer (first ⊓ second : Set GroupType),
        element ∉ first ⊓ second ∧ actorElement • element = element) := by
  classical
  have actor_pgroup : IsPGroup prime ActorType := by
    intro element
    exact ⟨1, by simpa using exponent element⟩
  let intersection := first ⊓ second
  let firstNormalizer := first ⊓ Subgroup.normalizer (intersection : Set GroupType)
  let secondNormalizer := second ⊓ Subgroup.normalizer (intersection : Set GroupType)
  have intersection_invariant : ∀ actorElement : ActorType, ∀ element ∈ intersection,
      actorElement • element ∈ intersection := by
    intro actorElement element member
    exact ⟨first_invariant actorElement element member.1,
      second_invariant actorElement element member.2⟩
  have normalizer_invariant := normalizer_invariant_of_invariant
    intersection intersection_invariant
  have firstNormalizer_invariant : ∀ actorElement : ActorType,
      ∀ element ∈ firstNormalizer, actorElement • element ∈ firstNormalizer := by
    intro actorElement element member
    exact ⟨first_invariant actorElement element member.1,
      normalizer_invariant actorElement element member.2⟩
  have secondNormalizer_invariant : ∀ actorElement : ActorType,
      ∀ element ∈ secondNormalizer, actorElement • element ∈ secondNormalizer := by
    intro actorElement element member
    exact ⟨second_invariant actorElement element member.1,
      normalizer_invariant actorElement element member.2⟩
  have firstNormalizer_coprime : Nat.Coprime prime (Nat.card firstNormalizer) :=
    prime_coprime_pgroup_card prime groupPrime prime_prime groupPrime_prime distinct
      (first_pgroup.to_le inf_le_left)
  have secondNormalizer_coprime : Nat.Coprime prime (Nat.card secondNormalizer) :=
    prime_coprime_pgroup_card prime groupPrime prime_prime groupPrime_prime distinct
      (second_pgroup.to_le inf_le_left)
  have first_growth := pgroup_normalizer_strict_growth groupPrime groupPrime_prime
    first intersection first_pgroup first_proper
  have second_growth := pgroup_normalizer_strict_growth groupPrime groupPrime_prime
    second intersection second_pgroup second_proper
  obtain ⟨firstActorSubgroup, first_cyclic, first_escape⟩ :=
    exists_cyclic_quotient_fixed_points_escape ActorType prime prime_prime actor_pgroup
      firstNormalizer intersection firstNormalizer_invariant firstNormalizer_coprime
      first_growth.not_ge
  obtain ⟨secondActorSubgroup, second_cyclic, second_escape⟩ :=
    exists_cyclic_quotient_fixed_points_escape ActorType prime prime_prime actor_pgroup
      secondNormalizer intersection secondNormalizer_invariant secondNormalizer_coprime
      second_growth.not_ge
  obtain ⟨actorElement, nonidentity, first_member, second_member⟩ :=
    cyclic_quotient_pair_intersection_nontrivial prime prime_prime ActorType exponent
      large firstActorSubgroup secondActorSubgroup first_cyclic second_cyclic
  refine ⟨actorElement, nonidentity, ?_, ?_⟩
  · have witness : ∃ element ∈ firstNormalizer ⊓
        FixedPoints.subgroup firstActorSubgroup GroupType, element ∉ intersection := by
      by_contra! all_contained
      exact first_escape all_contained
    obtain ⟨element, member, outside⟩ := witness
    exact ⟨element, member.1, outside, member.2 ⟨actorElement, first_member⟩⟩
  · have witness : ∃ element ∈ secondNormalizer ⊓
        FixedPoints.subgroup secondActorSubgroup GroupType, element ∉ intersection := by
      by_contra! all_contained
      exact second_escape all_contained
    obtain ⟨element, member, outside⟩ := witness
    exact ⟨element, member.1, outside, member.2 ⟨actorElement, second_member⟩⟩

end CFSG.SignalizerFunctor.Helpers
