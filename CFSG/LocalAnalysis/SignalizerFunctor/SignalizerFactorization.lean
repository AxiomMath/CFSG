module

public import CFSG.LocalAnalysis.SignalizerFunctor.MinimalIncompleteSolvable
public import CFSG.LocalAnalysis.SignalizerFunctor.SignalizerCoreControl

public section

open CFSG.Open

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]

@[expose] def signalizerNormalizerCompletion (prime rank : ℕ) (actor : Subgroup GroupType)
    (values : Subgroup GroupType → Subgroup GroupType) (target : Subgroup GroupType) :
    Subgroup GroupType :=
  ⨆ selected ∈ signalizerFunctorEk prime rank actor,
    signalizerRestriction values (Subgroup.normalizer (target : Set GroupType)) selected

@[expose] def signalizerPrimeCompletion (prime rank : ℕ) (actor : Subgroup GroupType)
    (values : Subgroup GroupType → Subgroup GroupType) (primes : Set ℕ) : Subgroup GroupType :=
  ⨆ selected ∈ signalizerFunctorEk prime rank actor,
    signalizerPrimeValue prime rank actor values primes selected

@[expose] def signalizerNormalizerFactorization (prime rank groupPrime : ℕ) (actor : Subgroup GroupType)
    (values : Subgroup GroupType → Subgroup GroupType) (model : Subgroup GroupType) : Prop :=
  ∀ target : Subgroup GroupType, target ≠ ⊥ →
    solvableSignalizerCompatible prime rank actor values target → IsPGroup groupPrime target →
    let localCompletion := signalizerNormalizerCompletion prime rank actor values target
    ∃ element : signalizerCommonFixed prime rank actor values,
      localCompletion =
        (primeSetCore (GroupType := localCompletion) ({groupPrime}ᶜ)).map localCompletion.subtype ⊔
          (localCompletion ⊓ conjugateSubgroup element.val model)

theorem signalizer_factorization_model_prime_part
    (prime rank groupPrime : ℕ) (prime_prime : prime.Prime) (groupPrime_prime : groupPrime.Prime)
    (actor model : Subgroup GroupType) (elementary : IsElemAbelian prime actor)
    (large : prime ^ (rank + 1) ≤ Nat.card actor)
    (values : Subgroup GroupType → Subgroup GroupType)
    (conditions : SolvableSignalizerConditions prime rank actor values)
    (locally_complete : solvableSignalizerLocallyComplete prime rank actor values)
    (prime_member : groupPrime ∈ signalizerSpectrum prime rank actor values)
    (factorization : signalizerNormalizerFactorization prime rank groupPrime actor values model) :
    groupPrime ∣ Nat.card model := by
  obtain ⟨_, selected, member, divides⟩ := prime_member
  let target := values selected
  obtain ⟨sylow, normalized, nontrivial⟩ := normalized_subgroup_invariant_sylow_nontrivial
    prime groupPrime prime_prime groupPrime_prime actor target
    (elementary_abelian_isPGroup prime actor elementary) (conditions.normalized selected member)
    (conditions.coprime selected member) divides
  let embedded := (sylow : Subgroup target).map target.subtype
  have embedded_pgroup : IsPGroup groupPrime embedded := sylow.isPGroup'.map target.subtype
  have embedded_compatible := solvable_signalizer_compatible_of_le prime rank actor values target
    embedded (solvable_signalizer_value_compatible prime rank actor values conditions selected member)
    (Subgroup.map_subtype_le _) normalized
  have complete := locally_complete.1 embedded nontrivial embedded_compatible
  have control := signalizer_normalizer_completion_control prime rank prime_prime actor embedded
    elementary large values conditions.coprime embedded_compatible.1 complete.1
  obtain ⟨element, local_factorization⟩ := factorization embedded nontrivial embedded_compatible
    embedded_pgroup
  have contained := normal_prime_subgroup_le_ambient_supplement groupPrime groupPrime_prime
    (signalizerNormalizerCompletion prime rank actor values embedded) embedded
    (conjugateSubgroup element.val model) control.2.1 control.2.2.1 embedded_pgroup local_factorization
  let : Fact groupPrime.Prime := ⟨groupPrime_prime⟩
  have embedded_divides : groupPrime ∣ Nat.card embedded := by
    rcases embedded_pgroup.card_eq_or_dvd with cardinality | divides
    · exact (nontrivial ((Subgroup.eq_bot_iff_card embedded).mpr cardinality)).elim
    · exact divides
  have model_divides := embedded_divides.trans (Subgroup.card_dvd_of_le contained)
  rwa [conjugate_subgroup_card] at model_divides

theorem signalizer_factorization_invariant_sylow_exists
    (prime rank groupPrime : ℕ) (prime_prime : prime.Prime) (groupPrime_prime : groupPrime.Prime)
    (actor model : Subgroup GroupType) (elementary : IsElemAbelian prime actor)
    (large : prime ^ (rank + 1) ≤ Nat.card actor)
    (values : Subgroup GroupType → Subgroup GroupType)
    (conditions : SolvableSignalizerConditions prime rank actor values)
    (locally_complete : solvableSignalizerLocallyComplete prime rank actor values)
    (prime_member : groupPrime ∈ signalizerSpectrum prime rank actor values)
    (model_compatible : solvableSignalizerCompatible prime rank actor values model)
    (factorization : signalizerNormalizerFactorization prime rank groupPrime actor values model) :
    let embeddedCore := (twoStageCore (GroupType := model) groupPrime).map model.subtype
    ∃ sylow : Sylow groupPrime embeddedCore,
      actor ≤ Subgroup.normalizer
        (((sylow : Subgroup embeddedCore).map embeddedCore.subtype : Subgroup GroupType) : Set GroupType) ∧
      (sylow : Subgroup embeddedCore).map embeddedCore.subtype ≠ ⊥ := by
  have rank_large : prime ^ rank ≤ Nat.card actor := by
    apply le_trans _ large
    rw [pow_succ]
    exact Nat.le_mul_of_pos_right _ prime_prime.pos
  have model_coprime := signalizer_subgroup_coprime prime rank prime_prime actor elementary rank_large
    values conditions.coprime model model_compatible.1.1 model_compatible.1.2
  have model_divides := signalizer_factorization_model_prime_part prime rank groupPrime prime_prime
    groupPrime_prime actor model elementary large values conditions locally_complete prime_member factorization
  exact invariant_two_stage_sylow_nontrivial prime groupPrime prime_prime groupPrime_prime actor model
    (elementary_abelian_isPGroup prime actor elementary) model_compatible.1.1 model_coprime
    model_compatible.2 model_divides

theorem signalizer_factorization_auxiliary_center
    (prime rank groupPrime : ℕ) (groupPrime_prime : groupPrime.Prime)
    (actor model : Subgroup GroupType) (values : Subgroup GroupType → Subgroup GroupType)
    (model_compatible : solvableSignalizerCompatible prime rank actor values model)
    (locally_complete : solvableSignalizerLocallyComplete prime rank actor values)
    (sylow : Sylow groupPrime
      ((twoStageCore (GroupType := model) groupPrime).map model.subtype))
    (normalized : actor ≤ Subgroup.normalizer
      (((sylow : Subgroup ((twoStageCore (GroupType := model) groupPrime).map model.subtype)).map
        ((twoStageCore (GroupType := model) groupPrime).map model.subtype).subtype : Subgroup GroupType) :
          Set GroupType))
    (nontrivial : (sylow : Subgroup ((twoStageCore (GroupType := model) groupPrime).map model.subtype)).map
      ((twoStageCore (GroupType := model) groupPrime).map model.subtype).subtype ≠ ⊥) :
    let embeddedCore := (twoStageCore (GroupType := model) groupPrime).map model.subtype
    let embedded := (sylow : Subgroup embeddedCore).map embeddedCore.subtype
    let center := (Subgroup.center embedded).map embedded.subtype
    center ≠ ⊥ ∧ IsMulCommutative center ∧ IsPGroup groupPrime center ∧
      solvableSignalizerCompatible prime rank actor values center ∧
      solvableSignalizerCompatible prime rank actor values
        (signalizerNormalizerCompletion prime rank actor values center) := by
  let embeddedCore := (twoStageCore (GroupType := model) groupPrime).map model.subtype
  let embedded := (sylow : Subgroup embeddedCore).map embeddedCore.subtype
  let center := (Subgroup.center embedded).map embedded.subtype
  have center_properties := normalized_prime_subgroup_center_nontrivial groupPrime groupPrime_prime
    actor embedded normalized (sylow.isPGroup'.map embeddedCore.subtype) nontrivial
  have center_le : center ≤ model := (Subgroup.map_subtype_le _).trans
    ((Subgroup.map_subtype_le _).trans (Subgroup.map_subtype_le _))
  have center_compatible := solvable_signalizer_compatible_of_le prime rank actor values model center
    model_compatible center_le center_properties.2.2.2
  exact ⟨center_properties.1, center_properties.2.1, center_properties.2.2.1, center_compatible,
    locally_complete.1 center center_properties.1 center_compatible⟩

end CFSG.SignalizerFunctor.Helpers
