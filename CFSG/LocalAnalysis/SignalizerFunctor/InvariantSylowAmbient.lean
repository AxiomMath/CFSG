module

public import CFSG.LocalAnalysis.SignalizerFunctor.TwoStageSylowNormalizers

public section

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

open scoped Pointwise

variable {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]

omit [Finite GroupType] in
theorem characteristic_subgroup_map_normalized (actor parent : Subgroup GroupType)
    (normalized : actor ≤ Subgroup.normalizer (parent : Set GroupType))
    (internal : Subgroup parent) [internal.Characteristic] :
    actor ≤ Subgroup.normalizer (internal.map parent.subtype : Set GroupType) :=
  normalized.trans (normalizer_le_normalizer_characteristic parent internal)

theorem normalized_subgroup_invariant_sylow
    (prime groupPrime : ℕ) (prime_prime : prime.Prime) (groupPrime_prime : groupPrime.Prime)
    (actor target : Subgroup GroupType) (actor_pgroup : IsPGroup prime actor)
    (normalized : actor ≤ Subgroup.normalizer (target : Set GroupType))
    (coprime : Nat.Coprime prime (Nat.card target)) :
    ∃ sylow : Sylow groupPrime target,
      actor ≤ Subgroup.normalizer
        (((sylow : Subgroup target).map target.subtype : Subgroup GroupType) : Set GroupType) := by
  let _action := conjugationAction actor target normalized
  obtain ⟨sylow, fixed⟩ := invariant_sylow_exists prime groupPrime prime_prime groupPrime_prime
    actor_pgroup coprime
  refine ⟨sylow, invariant_subgroup_map_normalized actor target normalized _ ?_⟩
  change ∀ actorElement : actor, ∀ element ∈ (sylow : Subgroup target),
    actorElement • element ∈ (sylow : Subgroup target)
  intro actorElement element member
  have equal : actorElement • (sylow : Subgroup target) = (sylow : Subgroup target) := by
    rw [← Sylow.pointwise_smul_def, fixed actorElement]
  rw [← equal]
  exact Subgroup.smul_mem_pointwise_smul element actorElement _ member

theorem normalized_subgroup_invariant_sylow_nontrivial
    (prime groupPrime : ℕ) (prime_prime : prime.Prime) (groupPrime_prime : groupPrime.Prime)
    (actor target : Subgroup GroupType) (actor_pgroup : IsPGroup prime actor)
    (normalized : actor ≤ Subgroup.normalizer (target : Set GroupType))
    (coprime : Nat.Coprime prime (Nat.card target)) (divides : groupPrime ∣ Nat.card target) :
    ∃ sylow : Sylow groupPrime target,
      actor ≤ Subgroup.normalizer
        (((sylow : Subgroup target).map target.subtype : Subgroup GroupType) : Set GroupType) ∧
      (sylow : Subgroup target).map target.subtype ≠ ⊥ := by
  obtain ⟨sylow, normalized⟩ := normalized_subgroup_invariant_sylow prime groupPrime prime_prime
    groupPrime_prime actor target actor_pgroup normalized coprime
  refine ⟨sylow, normalized, ?_⟩
  intro trivial
  have cardinality := (Subgroup.eq_bot_iff_card _).mp trivial
  rw [Subgroup.card_map_of_injective target.subtype_injective] at cardinality
  let : Fact groupPrime.Prime := ⟨groupPrime_prime⟩
  have sylow_divides : groupPrime ∣ Nat.card (sylow : Subgroup target) := by
    simpa only [pow_one] using sylow.pow_dvd_card_of_pow_dvd_card (n := 1)
      (by simpa only [pow_one] using divides)
  rw [cardinality] at sylow_divides
  exact groupPrime_prime.not_dvd_one sylow_divides

theorem invariant_two_stage_sylow_nontrivial
    (prime groupPrime : ℕ) (prime_prime : prime.Prime) (groupPrime_prime : groupPrime.Prime)
    (actor target : Subgroup GroupType) (actor_pgroup : IsPGroup prime actor)
    (normalized : actor ≤ Subgroup.normalizer (target : Set GroupType))
    (coprime : Nat.Coprime prime (Nat.card target))
    (solvable : Group.IsSolvable target) (divides : groupPrime ∣ Nat.card target) :
    let embeddedCore := (twoStageCore (GroupType := target) groupPrime).map target.subtype
    ∃ sylow : Sylow groupPrime embeddedCore,
      actor ≤ Subgroup.normalizer
        (((sylow : Subgroup embeddedCore).map embeddedCore.subtype : Subgroup GroupType) : Set GroupType) ∧
      (sylow : Subgroup embeddedCore).map embeddedCore.subtype ≠ ⊥ := by
  let := solvable
  let embeddedCore := (twoStageCore (GroupType := target) groupPrime).map target.subtype
  let _characteristic := two_stage_core_characteristic (GroupType := target) groupPrime
  have core_normalized := characteristic_subgroup_map_normalized actor target normalized
    (twoStageCore (GroupType := target) groupPrime)
  have core_coprime : Nat.Coprime prime (Nat.card embeddedCore) :=
    coprime.of_dvd_right (Subgroup.card_dvd_of_le (Subgroup.map_subtype_le _))
  have core_divides : groupPrime ∣ Nat.card embeddedCore := by
    rw [Subgroup.card_map_of_injective target.subtype_injective]
    exact two_stage_core_has_prime_part groupPrime groupPrime_prime divides
  exact normalized_subgroup_invariant_sylow_nontrivial prime groupPrime prime_prime groupPrime_prime
    actor embeddedCore actor_pgroup core_normalized core_coprime core_divides

end CFSG.SignalizerFunctor.Helpers
