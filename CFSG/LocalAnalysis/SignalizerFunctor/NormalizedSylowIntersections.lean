module

public import CFSG.LocalAnalysis.SignalizerFunctor.LocalSylowIntersections

public section

universe actorUniverse groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

open scoped Pointwise

variable {ActorType : Type actorUniverse} [Group ActorType]
variable {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]
variable [MulDistribMulAction ActorType GroupType]

omit [Finite GroupType] in
theorem invariant_sylow_subgroup_iff (prime : ℕ) (sylow : Sylow prime GroupType) :
    (∀ actorElement : ActorType, actorElement • sylow = sylow) ↔
      ∀ actorElement : ActorType, ∀ element ∈ (sylow : Subgroup GroupType),
        actorElement • element ∈ (sylow : Subgroup GroupType) := by
  constructor
  · intro fixed actorElement element member
    have equal : actorElement • (sylow : Subgroup GroupType) = sylow := by
      rw [← Sylow.pointwise_smul_def, fixed actorElement]
    rw [← equal]
    exact Subgroup.smul_mem_pointwise_smul element actorElement _ member
  · intro invariant actorElement
    apply Sylow.ext
    rw [Sylow.pointwise_smul_def]
    change (sylow : Subgroup GroupType).map (MulDistribMulAction.toMonoidHom GroupType actorElement) = _
    apply le_antisymm
    · rintro element ⟨original, member, rfl⟩
      exact invariant actorElement original member
    · intro element member
      refine ⟨actorElement⁻¹ • element, invariant actorElement⁻¹ element member, ?_⟩
      exact smul_inv_smul actorElement element

theorem fixed_normalized_invariant_sylow_intersection
    (prime groupPrime : ℕ) (prime_prime : prime.Prime) (groupPrime_prime : groupPrime.Prime)
    (actor_pgroup : IsPGroup prime ActorType) (coprime : Nat.Coprime prime (Nat.card GroupType))
    (sylow : Sylow groupPrime GroupType)
    (fixed : ∀ actorElement : ActorType, actorElement • sylow = sylow)
    (subgroup : Subgroup GroupType)
    (invariant : ∀ actorElement : ActorType, ∀ element ∈ subgroup, actorElement • element ∈ subgroup)
    (fixed_normalized : FixedPoints.subgroup ActorType GroupType ≤
      Subgroup.normalizer (subgroup : Set GroupType)) :
    ∃ internalSylow : Sylow groupPrime subgroup,
      (internalSylow : Subgroup subgroup).map subgroup.subtype =
        (sylow : Subgroup GroupType) ⊓ subgroup ∧
      ∀ actorElement : ActorType, ∀ element ∈ (sylow : Subgroup GroupType) ⊓ subgroup,
        actorElement • element ∈ (sylow : Subgroup GroupType) ⊓ subgroup := by
  let : Fact groupPrime.Prime := ⟨groupPrime_prime⟩
  let _subgroupAction := invariantSubgroupAction subgroup invariant
  obtain ⟨internalSylow, internal_fixed⟩ := invariant_sylow_exists prime groupPrime prime_prime
    groupPrime_prime actor_pgroup (coprime.of_dvd_right subgroup.card_subgroup_dvd_card)
  let embedded := (internalSylow : Subgroup subgroup).map subgroup.subtype
  have embedded_invariant : ∀ actorElement : ActorType, ∀ element ∈ embedded,
      actorElement • element ∈ embedded := by
    rintro actorElement element ⟨original, member, rfl⟩
    exact Subgroup.mem_map_of_mem subgroup.subtype
      ((invariant_sylow_subgroup_iff groupPrime internalSylow).mp internal_fixed actorElement original member)
  have embedded_pgroup : IsPGroup groupPrime embedded := internalSylow.isPGroup'.map subgroup.subtype
  obtain ⟨extendedSylow, extended_contains, extended_fixed⟩ := invariant_sylow_containing prime groupPrime
    prime_prime groupPrime_prime actor_pgroup coprime embedded embedded_pgroup embedded_invariant
  have extended_intersection : (extendedSylow : Subgroup GroupType) ⊓ subgroup = embedded := by
    have internal_pgroup : IsPGroup groupPrime ((extendedSylow : Subgroup GroupType).subgroupOf subgroup) :=
      (extendedSylow.isPGroup'.to_le
        (show (extendedSylow : Subgroup GroupType) ⊓ subgroup ≤ extendedSylow from inf_le_left)).of_equiv
        ((Subgroup.subgroupOfEquivOfLe
          (show (extendedSylow : Subgroup GroupType) ⊓ subgroup ≤ subgroup from inf_le_right)).symm.trans
          (MulEquiv.subgroupCongr (show
            ((extendedSylow : Subgroup GroupType) ⊓ subgroup).subgroupOf subgroup =
              (extendedSylow : Subgroup GroupType).subgroupOf subgroup from by
                ext element
                exact and_iff_left element.property)))
    have internal_contains : (internalSylow : Subgroup subgroup) ≤
        (extendedSylow : Subgroup GroupType).subgroupOf subgroup := by
      intro element member
      exact extended_contains (Subgroup.mem_map_of_mem subgroup.subtype member)
    have equal := internalSylow.is_maximal' internal_pgroup internal_contains
    have mapped_eq := congrArg (Subgroup.map subgroup.subtype) equal
    rw [Subgroup.subgroupOf_map_subtype] at mapped_eq
    exact mapped_eq
  obtain ⟨conjugator, conjugates, conjugator_fixed⟩ := invariant_sylows_conjugate_by_fixed_element
    prime groupPrime prime_prime groupPrime_prime ActorType actor_pgroup GroupType coprime
    extendedSylow sylow extended_fixed fixed
  have subgroup_preserved : conjugateSubgroup conjugator subgroup = subgroup :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (fixed_normalized conjugator_fixed)
  have extended_eq : conjugateSubgroup conjugator (extendedSylow : Subgroup GroupType) = sylow :=
    congrArg (fun candidate : Sylow groupPrime GroupType => (candidate : Subgroup GroupType)) conjugates
  have conjugated_eq := congrArg (Subgroup.map (MulAut.conj conjugator).toMonoidHom) extended_intersection
  rw [Subgroup.map_inf _ _ _ (MulAut.conj conjugator).injective] at conjugated_eq
  change conjugateSubgroup conjugator (extendedSylow : Subgroup GroupType) ⊓
    conjugateSubgroup conjugator subgroup = conjugateSubgroup conjugator embedded at conjugated_eq
  rw [extended_eq, subgroup_preserved] at conjugated_eq
  have intersection_card : Nat.card ((sylow : Subgroup GroupType).subgroupOf subgroup) =
      Nat.card (internalSylow : Subgroup subgroup) := by
    rw [← Subgroup.card_map_of_injective subgroup.subtype_injective,
      Subgroup.subgroupOf_map_subtype, conjugated_eq, conjugate_subgroup_card,
      Subgroup.card_map_of_injective subgroup.subtype_injective]
  have intersection_pgroup : IsPGroup groupPrime ((sylow : Subgroup GroupType).subgroupOf subgroup) :=
    (sylow.isPGroup'.to_le
      (show (sylow : Subgroup GroupType) ⊓ subgroup ≤ sylow from inf_le_left)).of_equiv
      ((Subgroup.subgroupOfEquivOfLe
        (show (sylow : Subgroup GroupType) ⊓ subgroup ≤ subgroup from inf_le_right)).symm.trans
        (MulEquiv.subgroupCongr (show ((sylow : Subgroup GroupType) ⊓ subgroup).subgroupOf subgroup =
          (sylow : Subgroup GroupType).subgroupOf subgroup from by
            ext element
            exact and_iff_left element.property)))
  obtain ⟨result, result_eq⟩ := pgroup_sylow_of_card_eq groupPrime groupPrime_prime _
    intersection_pgroup internalSylow intersection_card
  refine ⟨result, ?_, ?_⟩
  · rw [result_eq, Subgroup.subgroupOf_map_subtype]
  · intro actorElement element member
    exact ⟨(invariant_sylow_subgroup_iff groupPrime sylow).mp fixed actorElement element member.1,
      invariant actorElement element member.2⟩

end CFSG.SignalizerFunctor.Helpers
