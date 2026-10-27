module

public import CFSG.LocalAnalysis.SignalizerFunctor.ProductPrimeParts
public import CFSG.LocalAnalysis.SignalizerFunctor.SolvablePrimeCore
public import CFSG.LocalAnalysis.SignalizerFunctor.IteratedActionCommutators

public section

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType]

theorem conjugation_action_commutator_map (actor target : Subgroup GroupType)
    (normalized : actor ≤ Subgroup.normalizer (target : Set GroupType)) :
    let _action := conjugationAction actor target normalized
    (actionCommutator (ActorType := actor) (GroupType := target)).map target.subtype = ⁅target, actor⁆ := by
  let _action := conjugationAction actor target normalized
  change (actionCommutator (ActorType := actor) (GroupType := target)).map target.subtype = _
  apply le_antisymm
  · apply Subgroup.map_le_iff_le_comap.mpr
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨actorElement, element, rfl⟩
    have generated := Subgroup.commutator_mem_commutator (target.inv_mem element.property) actorElement.property
    change element.val⁻¹ * (actorElement.val * element.val * actorElement.val⁻¹) ∈ ⁅target, actor⁆
    simpa only [commutatorElement_def, inv_inv, mul_assoc] using generated
  · apply Subgroup.commutator_le.mpr
    intro element member actorElement actor_member
    have generated := Subgroup.mem_map_of_mem target.subtype
      (action_commutator_generator (⟨actorElement, actor_member⟩ : actor) (⟨element, member⟩ : target)⁻¹)
    change element⁻¹⁻¹ * (actorElement * element⁻¹ * actorElement⁻¹) ∈
      (actionCommutator (ActorType := actor) (GroupType := target)).map target.subtype at generated
    simpa only [commutatorElement_def, inv_inv, mul_assoc] using generated

theorem normalized_commutator_normalized (actor target : Subgroup GroupType)
    (normalized : actor ≤ Subgroup.normalizer (target : Set GroupType)) :
    actor ≤ Subgroup.normalizer ((⁅target, actor⁆ : Subgroup GroupType) : Set GroupType) := by
  let _action := conjugationAction actor target normalized
  have invariant := action_commutator_invariant (ActorType := actor) (GroupType := target)
  have embedded_invariant := invariant_subgroup_map_normalized actor target normalized
    (actionCommutator (ActorType := actor) (GroupType := target)) invariant
  rwa [conjugation_action_commutator_map actor target normalized] at embedded_invariant

theorem normalized_commutator_normal_in_target (actor target : Subgroup GroupType)
    (normalized : actor ≤ Subgroup.normalizer (target : Set GroupType)) :
    (⁅target, actor⁆.subgroupOf target).Normal := by
  let _action := conjugationAction actor target normalized
  let internal := actionCommutator (ActorType := actor) (GroupType := target)
  let _normal : internal.Normal := action_commutator_normal
  have equal : ⁅target, actor⁆.subgroupOf target = internal := by
    rw [← conjugation_action_commutator_map actor target normalized]
    exact Subgroup.comap_map_eq_self_of_injective target.subtype_injective internal
  rwa [equal]

theorem normalized_commutator_target_normalizes (actor target : Subgroup GroupType)
    (normalized : actor ≤ Subgroup.normalizer (target : Set GroupType)) :
    target ≤ Subgroup.normalizer ((⁅target, actor⁆ : Subgroup GroupType) : Set GroupType) := by
  let _normal := normalized_commutator_normal_in_target actor target normalized
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer
    (commutator_le_of_normalizing target actor normalized)).mp inferInstance

theorem coprime_normalized_commutator_factorization [Finite GroupType]
    (prime : ℕ) (prime_prime : prime.Prime) (actor target : Subgroup GroupType)
    (actor_pgroup : IsPGroup prime actor) (normalized : actor ≤ Subgroup.normalizer (target : Set GroupType))
    (coprime : Nat.Coprime prime (Nat.card target)) :
    ⁅target, actor⁆ ⊔ (target ⊓ Subgroup.centralizer (actor : Set GroupType)) = target := by
  let _action := conjugationAction actor target normalized
  have factorization := coprime_action_commutator_factorization prime prime_prime actor_pgroup coprime
  have mapped_eq := congrArg (Subgroup.map target.subtype) factorization
  rwa [Subgroup.map_sup, conjugation_action_commutator_map actor target normalized,
    conjugation_fixed_subgroup_map actor target normalized, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype] at mapped_eq

theorem coprime_normalized_commutator_product [Finite GroupType]
    (prime : ℕ) (prime_prime : prime.Prime) (actor target : Subgroup GroupType)
    (actor_pgroup : IsPGroup prime actor) (normalized : actor ≤ Subgroup.normalizer (target : Set GroupType))
    (coprime : Nat.Coprime prime (Nat.card target)) :
    subgroupProduct ⁅target, actor⁆ (target ⊓ Subgroup.centralizer (actor : Set GroupType)) = (target : Set GroupType) := by
  have factorization := coprime_normalized_commutator_factorization prime prime_prime actor target actor_pgroup normalized coprime
  have first_le := commutator_le_of_normalizing target actor normalized
  have factor_normalizes : target ⊓ Subgroup.centralizer (actor : Set GroupType) ≤
      Subgroup.normalizer ((⁅target, actor⁆ : Subgroup GroupType) : Set GroupType) :=
    inf_le_left.trans (normalized_commutator_target_normalizes actor target normalized)
  apply (subgroup_product_eq_subgroup_iff target _ _ first_le inf_le_left).mpr
  intro element member
  exact (mem_sup_of_normalizing _ _ factor_normalizes element).mp (by rwa [factorization])

theorem coprime_normalized_commutator_idempotent [Finite GroupType]
    (prime : ℕ) (prime_prime : prime.Prime) (actor target : Subgroup GroupType)
    (actor_pgroup : IsPGroup prime actor) (normalized : actor ≤ Subgroup.normalizer (target : Set GroupType))
    (coprime : Nat.Coprime prime (Nat.card target)) : ⁅⁅target, actor⁆, actor⁆ = ⁅target, actor⁆ := by
  let _action := conjugationAction actor target normalized
  let internal := actionCommutator (ActorType := actor) (GroupType := target)
  have internal_eq := conjugation_action_commutator_map actor target normalized
  have idempotent := coprime_action_commutator_idempotent prime prime_prime actor_pgroup coprime
  have mapped_eq := congrArg (Subgroup.map target.subtype) idempotent
  have iterated_eq : (invariantActionCommutator internal action_commutator_invariant).map target.subtype =
      ⁅internal.map target.subtype, actor⁆ := by
    let _internalAction := invariantSubgroupAction internal action_commutator_invariant
    change ((actionCommutator (ActorType := actor) (GroupType := internal)).map internal.subtype).map target.subtype = _
    rw [Subgroup.map_map]
    apply le_antisymm
    · apply Subgroup.map_le_iff_le_comap.mpr
      apply (Subgroup.closure_le _).mpr
      rintro _ ⟨actorElement, element, rfl⟩
      have generated := Subgroup.commutator_mem_commutator
        (Subgroup.mem_map_of_mem target.subtype (internal.inv_mem element.property)) actorElement.property
      change element.val.val⁻¹ * (actorElement.val * element.val.val * actorElement.val⁻¹) ∈
        ⁅internal.map target.subtype, actor⁆
      simpa only [commutatorElement_def, Subgroup.coe_inv, MonoidHom.coe_ofClass, Subgroup.coe_subtype,
        inv_inv, mul_assoc] using generated
    · apply Subgroup.commutator_le.mpr
      rintro element ⟨original, original_member, rfl⟩ actorElement actor_member
      have generated := Subgroup.mem_map_of_mem (target.subtype.comp internal.subtype)
        (action_commutator_generator (⟨actorElement, actor_member⟩ : actor) (⟨original, original_member⟩ : internal)⁻¹)
      change original.val⁻¹⁻¹ * (actorElement * original.val⁻¹ * actorElement⁻¹) ∈
        (actionCommutator (ActorType := actor) (GroupType := internal)).map
          (target.subtype.comp internal.subtype) at generated
      change original.val * actorElement * original.val⁻¹ * actorElement⁻¹ ∈
        (actionCommutator (ActorType := actor) (GroupType := internal)).map (target.subtype.comp internal.subtype)
      simpa only [commutatorElement_def, inv_inv, mul_assoc] using generated
  rwa [iterated_eq, internal_eq] at mapped_eq

end CFSG.SignalizerFunctor.Helpers
