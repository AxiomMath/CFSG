module

public import CFSG.LocalAnalysis.SignalizerFunctor.OnePrimeCompleteness
public import CFSG.LocalAnalysis.SignalizerFunctor.SignalizerFactorization
public import CFSG.LocalAnalysis.SignalizerFunctor.CoprimeQuotientNormalizers
public import CFSG.LocalAnalysis.SignalizerFunctor.NormalComplementAbsorption
public import CFSG.LocalAnalysis.SignalizerFunctor.InvariantSylowSupplements

public section

open CFSG.Open

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]

omit [Finite GroupType] in
theorem signalizer_compatible_common_fixed_le (prime rank : ℕ) (actor target : Subgroup GroupType)
    (values : Subgroup GroupType → Subgroup GroupType)
    (compatible : signalizerCompatible prime rank actor values target) :
    target ⊓ Subgroup.centralizer (actor : Set GroupType) ≤
      signalizerCommonFixed prime rank actor values := by
  intro element member
  refine ⟨member.2, ?_⟩
  apply Subgroup.mem_iInf.mpr
  intro selected
  apply Subgroup.mem_iInf.mpr
  intro selected_member
  exact compatible.2 selected selected_member
    ⟨member.1, Subgroup.centralizer_le selected_member.1 member.2⟩

omit [Finite GroupType] in
theorem embedded_prime_core_normal (parent : Subgroup GroupType) (primes : Set ℕ) :
    (((primeSetCore (GroupType := parent) primes).map parent.subtype).subgroupOf parent).Normal := by
  rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective parent.subtype_injective]
  exact prime_set_core_normal primes

theorem signalizer_normalizer_completion_model_intersection
    (prime rank : ℕ) (prime_prime : prime.Prime)
    (actor target model : Subgroup GroupType) (elementary : IsElemAbelian prime actor)
    (large : prime ^ (rank + 1) ≤ Nat.card actor)
    (values : Subgroup GroupType → Subgroup GroupType)
    (conditions : SolvableSignalizerConditions prime rank actor values)
    (target_compatible : signalizerCompatible prime rank actor values target)
    (model_compatible : signalizerCompatible prime rank actor values model)
    (complete : signalizerCompatible prime rank actor values
      (signalizerNormalizerCompletion prime rank actor values target)) :
    model ⊓ Subgroup.normalizer (target : Set GroupType) =
      signalizerNormalizerCompletion prime rank actor values target ⊓ model := by
  let completion := signalizerNormalizerCompletion prime rank actor values target
  have completion_le : completion ≤ Subgroup.normalizer (target : Set GroupType) :=
    iSup_le fun _ => iSup_le fun _ => inf_le_right
  have intersection_compatible := signalizer_compatible_inf prime rank actor values model
    (Subgroup.normalizer (target : Set GroupType)) model_compatible
    (normalizer_normalized actor target target_compatible.1)
  have control := signalizer_normalizer_completion_control prime rank prime_prime actor target
    elementary large values conditions.coprime target_compatible complete
  apply le_antisymm
  · exact le_inf (control.2.2.2 _ intersection_compatible inf_le_right) inf_le_left
  · exact le_inf inf_le_right (inf_le_left.trans completion_le)

theorem signalizer_normalizer_factorization_transfer
    (prime rank groupPrime : ℕ) (prime_prime : prime.Prime) (groupPrime_prime : groupPrime.Prime)
    (actor source model target : Subgroup GroupType) (elementary : IsElemAbelian prime actor)
    (large : prime ^ (rank + 1) ≤ Nat.card actor)
    (values : Subgroup GroupType → Subgroup GroupType)
    (conditions : SolvableSignalizerConditions prime rank actor values)
    (locally_complete : solvableSignalizerLocallyComplete prime rank actor values)
    (source_compatible : solvableSignalizerCompatible prime rank actor values source)
    (model_compatible : solvableSignalizerCompatible prime rank actor values model)
    (target_compatible : solvableSignalizerCompatible prime rank actor values target)
    (target_nontrivial : target ≠ ⊥) (target_pgroup : IsPGroup groupPrime target)
    (target_le : target ≤ model)
    (model_factorization : model =
      (primeSetCore (GroupType := model) ({groupPrime}ᶜ)).map model.subtype ⊔ (source ⊓ model))
    (normalizer_factorization :
      let completion := signalizerNormalizerCompletion prime rank actor values target
      completion = (primeSetCore (GroupType := completion) ({groupPrime}ᶜ)).map completion.subtype ⊔
        (completion ⊓ model)) :
    let completion := signalizerNormalizerCompletion prime rank actor values target
    ∃ element : signalizerCommonFixed prime rank actor values, element.val ∈ model ∧
      completion = (primeSetCore (GroupType := completion) ({groupPrime}ᶜ)).map completion.subtype ⊔
        (completion ⊓ conjugateSubgroup element.val source) := by
  let completion := signalizerNormalizerCompletion prime rank actor values target
  let modelCore := (primeSetCore (GroupType := model) ({groupPrime}ᶜ)).map model.subtype
  let completionCore :=
    (primeSetCore (GroupType := completion) ({groupPrime}ᶜ)).map completion.subtype
  change completion = completionCore ⊔ (completion ⊓ model) at normalizer_factorization
  have model_coprime := signalizer_subgroup_coprime prime rank prime_prime actor elementary
    ((pow_le_pow_right' prime_prime.one_le (Nat.le_succ rank)).trans large)
    values conditions.coprime model model_compatible.1.1 model_compatible.1.2
  have core_coprime : Nat.Coprime groupPrime (Nat.card modelCore) := by
    rw [Subgroup.card_map_of_injective model.subtype_injective]
    exact (prime_supported_complement_singleton_iff_coprime groupPrime groupPrime_prime _).mp
      (prime_set_core_supported ({groupPrime}ᶜ))
  obtain ⟨conjugator, fixed, target_in_source⟩ := invariant_prime_subgroup_into_coprime_supplement
    prime groupPrime prime_prime groupPrime_prime actor model modelCore (source ⊓ model) target
    (elementary_abelian_isPGroup prime actor elementary) model_compatible.1.1
    (normalizer_inf_of_le actor source model source_compatible.1.1 model_compatible.1.1)
    target_compatible.1.1 model_coprime (Subgroup.map_subtype_le _) inf_le_right target_le
    (embedded_prime_core_normal model ({groupPrime}ᶜ)) core_coprime model_factorization.symm
    target_pgroup
  have common_member := signalizer_compatible_common_fixed_le prime rank actor model values
    model_compatible.1 fixed
  let commonElement : signalizerCommonFixed prime rank actor values := ⟨conjugator, common_member⟩
  let conjugated := conjugateSubgroup conjugator source
  have model_preserved : conjugateSubgroup conjugator model = model :=
    conjugate_subgroup_eq_of_mem conjugator model fixed.1
  have core_preserved : conjugateSubgroup conjugator modelCore = modelCore := by
    let _characteristic := prime_set_core_characteristic (GroupType := model) ({groupPrime}ᶜ)
    have normalized := characteristic_subgroup_map_normalized model model Subgroup.le_normalizer
      (primeSetCore (GroupType := model) ({groupPrime}ᶜ))
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (normalized fixed.1)
  have conjugated_intersection : conjugateSubgroup conjugator (source ⊓ model) =
      conjugated ⊓ model := by
    rw [conjugateSubgroup, Subgroup.map_inf _ _ _ (MulAut.conj conjugator).injective]
    change conjugated ⊓ conjugateSubgroup conjugator model = _
    rw [model_preserved]
  rw [conjugated_intersection] at target_in_source
  have conjugated_factorization := congrArg (conjugateSubgroup conjugator) model_factorization
  change conjugateSubgroup conjugator model =
    (modelCore ⊔ source ⊓ model).map (MulAut.conj conjugator).toMonoidHom at conjugated_factorization
  rw [Subgroup.map_sup] at conjugated_factorization
  change conjugateSubgroup conjugator model =
    conjugateSubgroup conjugator modelCore ⊔ conjugateSubgroup conjugator (source ⊓ model)
    at conjugated_factorization
  rw [model_preserved, core_preserved, conjugated_intersection] at conjugated_factorization
  have normalizer_eq := ambient_normalizer_sup_coprime_kernel groupPrime groupPrime_prime model
    modelCore (conjugated ⊓ model) target (Subgroup.map_subtype_le _) inf_le_right
    (embedded_prime_core_normal model ({groupPrime}ᶜ)) core_coprime conjugated_factorization.symm
    target_in_source target_pgroup
  have complete := locally_complete.1 target target_nontrivial target_compatible
  have intersection_eq := signalizer_normalizer_completion_model_intersection prime rank prime_prime
    actor target model elementary large values conditions target_compatible.1 model_compatible.1
    complete.1
  rw [intersection_eq] at normalizer_eq
  have completion_le : completion ≤ Subgroup.normalizer (target : Set GroupType) :=
    iSup_le fun _ => iSup_le fun _ => inf_le_right
  have model_normalizer_le : model ⊓ Subgroup.normalizer (target : Set GroupType) ≤ completion := by
    rw [intersection_eq]
    exact inf_le_left
  let first := modelCore ⊓ Subgroup.normalizer (target : Set GroupType)
  let second := (conjugated ⊓ model) ⊓ Subgroup.normalizer (target : Set GroupType)
  have first_le : first ≤ completion :=
    (inf_le_inf_right _ (Subgroup.map_subtype_le _)).trans model_normalizer_le
  have second_le : second ≤ completion :=
    (inf_le_inf_right _ inf_le_right).trans model_normalizer_le
  have first_coprime : Nat.Coprime groupPrime (Nat.card first) :=
    core_coprime.of_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
  have second_normalizes : second ≤ Subgroup.normalizer (first : Set GroupType) := by
    let _characteristic := prime_set_core_characteristic (GroupType := model) ({groupPrime}ᶜ)
    have model_normalizes_core := characteristic_subgroup_map_normalized model model
      Subgroup.le_normalizer (primeSetCore (GroupType := model) ({groupPrime}ᶜ))
    exact normalizer_inf_of_le second modelCore (Subgroup.normalizer (target : Set GroupType))
      ((inf_le_left.trans inf_le_right).trans model_normalizes_core)
      (inf_le_right.trans Subgroup.le_normalizer)
  have absorption_whole : (completionCore ⊔ first) ⊔ second = completion := by
    rw [sup_assoc]
    rw [← normalizer_eq]
    exact normalizer_factorization.symm
  have absorbed := ambient_normal_complement_absorption groupPrime groupPrime_prime completion first
    second first_le second_le first_coprime second_normalizes absorption_whole
  change ∃ element : signalizerCommonFixed prime rank actor values, element.val ∈ model ∧
    completion = completionCore ⊔ (completion ⊓ conjugateSubgroup element.val source)
  refine ⟨commonElement, fixed.1, le_antisymm ?_ ?_⟩
  · calc
      completion = completionCore ⊔ second := absorbed.2.symm
      _ ≤ completionCore ⊔ (completion ⊓ conjugated) :=
        sup_le_sup le_rfl (le_inf second_le (inf_le_left.trans inf_le_left))
  · exact sup_le (Subgroup.map_subtype_le _) inf_le_left

end CFSG.SignalizerFunctor.Helpers
