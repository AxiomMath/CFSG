module

public import CFSG.LocalAnalysis.SignalizerFunctor.SignalizerModelFactorization
public import CFSG.LocalAnalysis.SignalizerFunctor.PrimeCoreConjugation

public section

open CFSG.Open

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]

theorem signalizer_value_factorization_absorption
    (prime rank groupPrime : ℕ) (prime_prime : prime.Prime) (groupPrime_prime : groupPrime.Prime)
    (actor completion source : Subgroup GroupType) (elementary : IsElemAbelian prime actor)
    (large : prime ^ (rank + 1) ≤ Nat.card actor)
    (values : Subgroup GroupType → Subgroup GroupType)
    (conditions : SolvableSignalizerConditions prime rank actor values)
    (completion_compatible : signalizerCompatible prime rank actor values completion)
    (source_normalized : actor ≤ Subgroup.normalizer (source : Set GroupType))
    (completion_factorization : completion =
      (primeSetCore (GroupType := completion) ({groupPrime}ᶜ)).map completion.subtype ⊔
        (completion ⊓ source))
    (selected : Subgroup GroupType) (member : selected ∈ signalizerFunctorEk prime rank actor)
    (value_factorization : values selected =
      (primeSetCore (GroupType := values selected) ({groupPrime}ᶜ)).map (values selected).subtype ⊔
        (completion ⊓ values selected)) :
    values selected =
      (primeSetCore (GroupType := values selected) ({groupPrime}ᶜ)).map (values selected).subtype ⊔
        (values selected ⊓ source) := by
  let value := values selected
  let valueCore := (primeSetCore (GroupType := value) ({groupPrime}ᶜ)).map value.subtype
  let completionCore := (primeSetCore (GroupType := completion) ({groupPrime}ᶜ)).map completion.subtype
  let first := completionCore ⊓ value
  let second := (completion ⊓ source) ⊓ value
  let _characteristic := prime_set_core_characteristic (GroupType := completion) ({groupPrime}ᶜ)
  have core_normalized := characteristic_subgroup_map_normalized actor completion completion_compatible.1
    (primeSetCore (GroupType := completion) ({groupPrime}ᶜ))
  have completion_normalizes_core := characteristic_subgroup_map_normalized completion completion
    Subgroup.le_normalizer (primeSetCore (GroupType := completion) ({groupPrime}ᶜ))
  have other_normalized := normalizer_inf_of_le actor completion source completion_compatible.1
    source_normalized
  have completion_coprime := signalizer_subgroup_coprime prime rank prime_prime actor elementary
    ((pow_le_pow_right' prime_prime.one_le (Nat.le_succ rank)).trans large) values conditions.coprime
    completion completion_compatible.1 completion_compatible.2
  have intersection_formula := signalizer_normal_product_value_intersection prime rank prime_prime
    actor completion completionCore (completion ⊓ source) elementary values conditions.central
    completion_compatible core_normalized other_normalized
    (inf_le_left.trans completion_normalizes_core)
    (completion_coprime.of_dvd_right (Subgroup.card_dvd_of_le inf_le_left))
    completion_factorization selected member
  change completion ⊓ value = first ⊔ second at intersection_formula
  have first_coprime : Nat.Coprime groupPrime (Nat.card first) := by
    have core_coprime : Nat.Coprime groupPrime (Nat.card completionCore) := by
      rw [Subgroup.card_map_of_injective completion.subtype_injective]
      exact (prime_supported_complement_singleton_iff_coprime groupPrime groupPrime_prime _).mp
        (prime_set_core_supported ({groupPrime}ᶜ))
    exact core_coprime.of_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
  have second_normalizes : second ≤ Subgroup.normalizer (first : Set GroupType) :=
    normalizer_inf_of_le second completionCore value
      ((inf_le_left.trans inf_le_left).trans completion_normalizes_core)
      (inf_le_right.trans Subgroup.le_normalizer)
  have whole : (valueCore ⊔ first) ⊔ second = value := by
    rw [sup_assoc, ← intersection_formula]
    exact value_factorization.symm
  have absorbed := ambient_normal_complement_absorption groupPrime groupPrime_prime value first second
    inf_le_right inf_le_right first_coprime second_normalizes whole
  apply le_antisymm
  · calc
      value = valueCore ⊔ second := absorbed.2.symm
      _ ≤ valueCore ⊔ (value ⊓ source) :=
        sup_le_sup le_rfl (le_inf inf_le_right (inf_le_left.trans inf_le_right))
  · exact sup_le (Subgroup.map_subtype_le _) inf_le_left

theorem signalizer_value_factorization_common_conjugate_cancel
    (prime rank groupPrime : ℕ) (actor source : Subgroup GroupType)
    (values : Subgroup GroupType → Subgroup GroupType)
    (balanced : ∀ selected ∈ signalizerFunctorEk prime rank actor,
      ∀ other ∈ signalizerFunctorEk prime rank actor,
        values selected ⊓ Subgroup.centralizer (other : Set GroupType) ≤ values other)
    (selected : Subgroup GroupType) (member : selected ∈ signalizerFunctorEk prime rank actor)
    (element : signalizerCommonFixed prime rank actor values)
    (factorization : values selected =
      (primeSetCore (GroupType := values selected) ({groupPrime}ᶜ)).map (values selected).subtype ⊔
        (values selected ⊓ conjugateSubgroup element.val source)) :
    values selected =
      (primeSetCore (GroupType := values selected) ({groupPrime}ᶜ)).map (values selected).subtype ⊔
        (values selected ⊓ source) := by
  let value := values selected
  let core := (primeSetCore (GroupType := value) ({groupPrime}ᶜ)).map value.subtype
  have value_preserved := signalizer_common_conjugation_value prime rank actor values balanced
    element⁻¹ selected member
  change conjugateSubgroup element.val⁻¹ value = value at value_preserved
  have core_preserved : conjugateSubgroup element.val⁻¹ core = core := by
    let _characteristic := prime_set_core_characteristic (GroupType := value) ({groupPrime}ᶜ)
    have normalized := normalizer_le_normalizer_characteristic value
      (primeSetCore (GroupType := value) ({groupPrime}ᶜ))
    have member_normalizer : element.val⁻¹ ∈ Subgroup.normalizer (value : Set GroupType) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mpr value_preserved
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (normalized member_normalizer)
  have mapped_eq := congrArg (Subgroup.map (MulAut.conj element.val⁻¹).toMonoidHom) factorization
  rw [Subgroup.map_sup, Subgroup.map_inf _ _ _ (MulAut.conj element.val⁻¹).injective] at mapped_eq
  change conjugateSubgroup element.val⁻¹ value = conjugateSubgroup element.val⁻¹ core ⊔
    (conjugateSubgroup element.val⁻¹ value ⊓
      conjugateSubgroup element.val⁻¹ (conjugateSubgroup element.val source)) at mapped_eq
  rw [value_preserved, core_preserved, conjugate_subgroup_inv_cancel] at mapped_eq
  exact mapped_eq

theorem signalizer_local_value_factorization
    (prime rank groupPrime : ℕ) (prime_prime : prime.Prime) (groupPrime_prime : groupPrime.Prime)
    (actor source model : Subgroup GroupType) (elementary : IsElemAbelian prime actor)
    (large : prime ^ (rank + 1) ≤ Nat.card actor)
    (values : Subgroup GroupType → Subgroup GroupType)
    (conditions : SolvableSignalizerConditions prime rank actor values)
    (locally_complete : solvableSignalizerLocallyComplete prime rank actor values)
    (source_compatible : solvableSignalizerCompatible prime rank actor values source)
    (model_compatible : solvableSignalizerCompatible prime rank actor values model)
    (model_factorization : model =
      (primeSetCore (GroupType := model) ({groupPrime}ᶜ)).map model.subtype ⊔ (source ⊓ model))
    (factorization : signalizerNormalizerFactorization prime rank groupPrime actor values model)
    (selected : Subgroup GroupType) (member : selected ∈ signalizerFunctorEk prime rank actor) :
    values selected =
      (primeSetCore (GroupType := values selected) ({groupPrime}ᶜ)).map (values selected).subtype ⊔
        (values selected ⊓ source) := by
  classical
  let value := values selected
  let valueCore := (primeSetCore (GroupType := value) ({groupPrime}ᶜ)).map value.subtype
  by_cases divides : groupPrime ∣ Nat.card value
  · obtain ⟨sylow, normalized, nontrivial⟩ := invariant_two_stage_sylow_nontrivial prime groupPrime
      prime_prime groupPrime_prime actor value (elementary_abelian_isPGroup prime actor elementary)
      (conditions.normalized selected member) (conditions.coprime selected member)
      (conditions.solvable selected member) divides
    let core := (twoStageCore (GroupType := value) groupPrime).map value.subtype
    let target := (sylow : Subgroup core).map core.subtype
    let completion := signalizerNormalizerCompletion prime rank actor values target
    have target_le : target ≤ value :=
      (Subgroup.map_subtype_le _).trans (Subgroup.map_subtype_le _)
    have value_compatible := solvable_signalizer_value_compatible prime rank actor values conditions selected member
    have target_compatible := solvable_signalizer_compatible_of_le prime rank actor values value target
      value_compatible target_le normalized
    have target_pgroup : IsPGroup groupPrime target := sylow.isPGroup'.map core.subtype
    have complete := locally_complete.1 target nontrivial target_compatible
    have control := signalizer_normalizer_completion_control prime rank prime_prime actor target elementary
      large values conditions.coprime target_compatible.1 complete.1
    have value_factorization := signalizer_two_stage_normalizer_completion_factorization prime rank
      groupPrime prime_prime groupPrime_prime actor value elementary large values conditions
      value_compatible.1 sylow normalized complete.1
    obtain ⟨element, completion_factorization⟩ := factorization target nontrivial target_compatible target_pgroup
    have target_model := normal_prime_subgroup_le_ambient_supplement groupPrime groupPrime_prime
      completion target (conjugateSubgroup element.val model) control.2.1 control.2.2.1 target_pgroup
      completion_factorization
    have conjugated_source := solvable_signalizer_compatible_conjugate prime rank actor source values
      source_compatible element
    have conjugated_model := solvable_signalizer_compatible_conjugate prime rank actor model values
      model_compatible element
    have conjugated_factorization := signalizer_model_factorization_conjugate prime rank groupPrime actor
      source model values model_factorization element
    obtain ⟨secondElement, _, transferred⟩ := signalizer_normalizer_factorization_transfer prime rank groupPrime
      prime_prime groupPrime_prime actor (conjugateSubgroup element.val source)
      (conjugateSubgroup element.val model) target elementary large values conditions locally_complete
      conjugated_source conjugated_model target_compatible nontrivial target_pgroup target_model
      conjugated_factorization completion_factorization
    let combinedElement := secondElement * element
    have combined_source : conjugateSubgroup secondElement.val (conjugateSubgroup element.val source) =
        conjugateSubgroup combinedElement.val source := conjugate_subgroup_mul _ _ _
    rw [combined_source] at transferred
    have combined_compatible := solvable_signalizer_compatible_conjugate prime rank actor source values
      source_compatible combinedElement
    have absorbed := signalizer_value_factorization_absorption prime rank groupPrime prime_prime groupPrime_prime
      actor completion (conjugateSubgroup combinedElement.val source) elementary large values conditions
      complete.1 combined_compatible.1.1 transferred selected member value_factorization
    exact signalizer_value_factorization_common_conjugate_cancel prime rank groupPrime actor source values
      conditions.balanced selected member combinedElement absorbed
  · have supported : primeSupported ({groupPrime}ᶜ) (Nat.card value) :=
      (prime_supported_complement_singleton_iff_coprime groupPrime groupPrime_prime _).mpr
        (groupPrime_prime.coprime_iff_not_dvd.mpr divides)
    have core_top : primeSetCore (GroupType := value) ({groupPrime}ᶜ) = ⊤ := by
      apply top_unique
      exact prime_set_core_contains ({groupPrime}ᶜ) ⊤ inferInstance (by rwa [Subgroup.card_top])
    change value = valueCore ⊔ (value ⊓ source)
    dsimp only [valueCore]
    rw [core_top, ← MonoidHom.range_eq_map, value.subtype_range, sup_eq_left.mpr inf_le_left]

end CFSG.SignalizerFunctor.Helpers
