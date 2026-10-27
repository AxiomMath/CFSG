module

public import CFSG.LocalAnalysis.SignalizerFunctor.InvariantFusion
public import CFSG.LocalAnalysis.SignalizerFunctor.NormalPrimeSupplements

public section

universe actorUniverse groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

open scoped Pointwise

variable {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]

theorem sylow_supplement_lift (prime : ℕ) (prime_prime : prime.Prime)
    (normal supplement : Subgroup GroupType) [normal.Normal]
    (normal_coprime : Nat.Coprime prime (Nat.card normal))
    (whole : normal ⊔ supplement = ⊤) (sylow : Sylow prime supplement) :
    ∃ lifted : Sylow prime GroupType,
      (lifted : Subgroup GroupType) = (sylow : Subgroup supplement).map supplement.subtype := by
  let : Fact prime.Prime := ⟨prime_prime⟩
  let embedded := (sylow : Subgroup supplement).map supplement.subtype
  have index_not_dvd : ¬ prime ∣ embedded.index := by
    rw [Subgroup.index_map_subtype]
    exact prime_prime.not_dvd_mul sylow.not_dvd_index
      (prime_prime.coprime_iff_not_dvd.mp (normal_coprime.of_dvd_right
        (supplement_index_dvd_normal_card normal supplement whole)))
  have pgroup : IsPGroup prime embedded := sylow.isPGroup'.map supplement.subtype
  exact ⟨pgroup.toSylow index_not_dvd, IsPGroup.toSylow_coe _ _⟩

omit [Finite GroupType] in
theorem normalized_subgroup_invariant_subgroup (actor parent subgroup : Subgroup GroupType)
    (parent_normalized : actor ≤ Subgroup.normalizer (parent : Set GroupType))
    (subgroup_normalized : actor ≤ Subgroup.normalizer (subgroup : Set GroupType)) :
    let _action := conjugationAction actor parent parent_normalized
    ∀ actorElement : actor, ∀ element ∈ subgroup.subgroupOf parent,
      actorElement • element ∈ subgroup.subgroupOf parent := by
  let _action := conjugationAction actor parent parent_normalized
  change ∀ actorElement : actor, ∀ element ∈ subgroup.subgroupOf parent,
    actorElement • element ∈ subgroup.subgroupOf parent
  intro actorElement element member
  exact Subgroup.le_normalizer_iff.mp subgroup_normalized actorElement.val actorElement.property
    element.val member

omit [Finite GroupType] in
theorem invariant_subgroup_sylow_fixed (actor parent : Subgroup GroupType)
    (normalized : actor ≤ Subgroup.normalizer (parent : Set GroupType))
    (prime : ℕ) (sylow : Sylow prime parent)
    (invariant : actor ≤ Subgroup.normalizer
      ((sylow : Subgroup parent).map parent.subtype : Set GroupType)) :
    let _action := conjugationAction actor parent normalized
    ∀ actorElement : actor, actorElement • sylow = sylow := by
  let _action := conjugationAction actor parent normalized
  change ∀ actorElement : actor, actorElement • sylow = sylow
  intro actorElement
  apply Sylow.ext
  apply Subgroup.map_injective parent.subtype_injective
  rw [Sylow.pointwise_smul_def]
  change ((sylow : Subgroup parent).map
    (MulDistribMulAction.toMonoidHom parent actorElement)).map parent.subtype = _
  rw [Subgroup.map_map]
  have hom_eq : parent.subtype.comp
      (MulDistribMulAction.toMonoidHom parent actorElement) =
      (MulAut.conj actorElement.val).toMonoidHom.comp parent.subtype := by
    ext element
    rfl
  rw [hom_eq, ← Subgroup.map_map]
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (invariant actorElement.property)

theorem invariant_prime_subgroup_into_coprime_supplement
    (prime groupPrime : ℕ) (prime_prime : prime.Prime) (groupPrime_prime : groupPrime.Prime)
    (actor parent normal supplement target : Subgroup GroupType)
    (actor_pgroup : IsPGroup prime actor)
    (parent_normalized : actor ≤ Subgroup.normalizer (parent : Set GroupType))
    (supplement_normalized : actor ≤ Subgroup.normalizer (supplement : Set GroupType))
    (target_normalized : actor ≤ Subgroup.normalizer (target : Set GroupType))
    (coprime : Nat.Coprime prime (Nat.card parent))
    (normal_le : normal ≤ parent) (supplement_le : supplement ≤ parent) (target_le : target ≤ parent)
    (internal_normal : (normal.subgroupOf parent).Normal)
    (normal_coprime : Nat.Coprime groupPrime (Nat.card normal))
    (whole : normal ⊔ supplement = parent) (pgroup : IsPGroup groupPrime target) :
    ∃ element ∈ parent ⊓ Subgroup.centralizer (actor : Set GroupType),
      target ≤ conjugateSubgroup element supplement := by
  let _action := conjugationAction actor parent parent_normalized
  let := internal_normal
  have internal_whole : normal.subgroupOf parent ⊔ supplement.subgroupOf parent = ⊤ := by
    rw [← Subgroup.subgroupOf_sup normal_le supplement_le, whole, Subgroup.subgroupOf_self]
  have internal_coprime : Nat.Coprime groupPrime (Nat.card (normal.subgroupOf parent)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe normal_le).toEquiv]
    exact normal_coprime
  have supplement_coprime : Nat.Coprime prime (Nat.card (supplement.subgroupOf parent)) :=
    coprime.of_dvd_right (supplement.subgroupOf parent).card_subgroup_dvd_card
  let internalSupplement := supplement.subgroupOf parent
  have supplement_invariant := normalized_subgroup_invariant_subgroup actor parent supplement
    parent_normalized supplement_normalized
  let _supplementAction := invariantSubgroupAction internalSupplement supplement_invariant
  obtain ⟨supplementSylow, supplement_fixed⟩ := invariant_sylow_exists prime groupPrime
    prime_prime groupPrime_prime actor_pgroup supplement_coprime
  obtain ⟨lifted, lifted_eq⟩ := sylow_supplement_lift groupPrime groupPrime_prime
    (normal.subgroupOf parent) internalSupplement internal_coprime internal_whole supplementSylow
  have lifted_fixed : ∀ actorElement : actor, actorElement • lifted = lifted := by
    intro actorElement
    apply Sylow.ext
    rw [Sylow.pointwise_smul_def, lifted_eq]
    change ((supplementSylow : Subgroup internalSupplement).map internalSupplement.subtype).map
      (MulDistribMulAction.toMonoidHom parent actorElement) = _
    rw [Subgroup.map_map]
    have hom_eq : (MulDistribMulAction.toMonoidHom parent actorElement).comp
        internalSupplement.subtype = internalSupplement.subtype.comp
          (MulDistribMulAction.toMonoidHom internalSupplement actorElement) := by
      ext element
      rfl
    rw [hom_eq, ← Subgroup.map_map]
    change ((actorElement • supplementSylow : Sylow groupPrime internalSupplement) :
      Subgroup internalSupplement).map internalSupplement.subtype = _
    rw [supplement_fixed]
  have target_invariant := normalized_subgroup_invariant_subgroup actor parent target
    parent_normalized target_normalized
  have internal_pgroup : IsPGroup groupPrime (target.subgroupOf parent) :=
    pgroup.of_equiv (Subgroup.subgroupOfEquivOfLe target_le).symm
  obtain ⟨targetSylow, target_contains, target_fixed⟩ := invariant_sylow_containing prime groupPrime
    prime_prime groupPrime_prime actor_pgroup coprime (target.subgroupOf parent)
    internal_pgroup target_invariant
  obtain ⟨conjugator, conjugates, fixed⟩ := invariant_sylows_conjugate_by_fixed_element prime groupPrime
    prime_prime groupPrime_prime actor actor_pgroup parent coprime lifted targetSylow
    lifted_fixed target_fixed
  have mapped_fixed : conjugator.val ∈ parent ⊓ Subgroup.centralizer (actor : Set GroupType) := by
    have member := Subgroup.mem_map_of_mem parent.subtype
      (show conjugator ∈ FixedPoints.subgroup actor parent from fixed)
    rw [conjugation_fixed_subgroup_map actor parent parent_normalized] at member
    exact member
  have sylow_le : (lifted : Subgroup parent) ≤ internalSupplement := by
    rw [lifted_eq]
    exact Subgroup.map_subtype_le _
  have conjugated_le := Subgroup.map_mono (f := (MulAut.conj conjugator).toMonoidHom) sylow_le
  have conjugate_eq : conjugateSubgroup conjugator (lifted : Subgroup parent) = targetSylow :=
    congrArg (fun sylow : Sylow groupPrime parent => (sylow : Subgroup parent)) conjugates
  change conjugateSubgroup conjugator (lifted : Subgroup parent) ≤
    conjugateSubgroup conjugator internalSupplement at conjugated_le
  rw [conjugate_eq] at conjugated_le
  have target_conjugated := Subgroup.map_mono (f := parent.subtype)
    (target_contains.trans conjugated_le)
  rw [Subgroup.map_subgroupOf_eq_of_le target_le, conjugate_subgroup_map,
    Subgroup.map_subgroupOf_eq_of_le supplement_le] at target_conjugated
  exact ⟨conjugator.val, mapped_fixed, target_conjugated⟩

end CFSG.SignalizerFunctor.Helpers
