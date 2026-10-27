module

public import CFSG.LocalAnalysis.SignalizerFunctor.SignalizerAuxiliaryProduct
public import CFSG.LocalAnalysis.SignalizerFunctor.RestrictedHallProductCompleteness
public import CFSG.LocalAnalysis.SignalizerFunctor.SignalizerFactorizationCommonNormalization

public section

open CFSG.Open

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]

omit [Finite GroupType] in
theorem normalized_conjugate_hull_product (parent first second target : Subgroup GroupType)
    (first_le : first ≤ parent) (second_normalizes : second ≤ Subgroup.normalizer (target : Set GroupType))
    (whole : subgroupProduct first second = (parent : Set GroupType)) :
    normalizedConjugateHull parent target = normalizedConjugateHull first target := by
  apply le_antisymm
  · apply iSup_le
    intro conjugator
    have decomposition : conjugator.val ∈ subgroupProduct first second := by
      rw [whole]
      exact conjugator.property
    obtain ⟨firstElement, first_member, secondElement, second_member, product⟩ := decomposition
    change conjugateSubgroup conjugator.val target ≤ _
    rw [← product, ← conjugate_subgroup_mul]
    exact (Subgroup.map_mono (f := (MulAut.conj firstElement).toMonoidHom)
      (normalized_conjugate_subgroup_le second target second_normalizes secondElement second_member)).trans
        (le_iSup_of_le (⟨firstElement, first_member⟩ : first) le_rfl)
  · apply iSup_le
    intro conjugator
    exact le_iSup_of_le (⟨conjugator.val, first_le conjugator.property⟩ : parent) le_rfl

theorem signalizer_factorization_source_normalizes_closure
    (prime rank groupPrime : ℕ) (prime_prime : prime.Prime) (groupPrime_prime : groupPrime.Prime)
    (actor source factor : Subgroup GroupType) (elementary : IsElemAbelian prime actor)
    (large : prime ^ (rank + 2) ≤ Nat.card actor)
    (values : Subgroup GroupType → Subgroup GroupType)
    (conditions : SolvableSignalizerConditions prime rank actor values)
    (locally_complete : solvableSignalizerLocallyComplete prime rank actor values)
    (prime_member : groupPrime ∈ signalizerSpectrum prime rank actor values)
    (source_compatible : signalizerCompatible prime rank actor values source)
    (source_normalizes : source ≤ Subgroup.normalizer (factor : Set GroupType))
    (local_factorization : ∀ selected ∈ signalizerFunctorEk prime rank actor,
      values selected =
        (primeSetCore (GroupType := values selected) ({groupPrime}ᶜ)).map (values selected).subtype ⊔
          (values selected ⊓ source)) :
    source ≤ Subgroup.normalizer
      (normalizedConjugateHull
        (signalizerPrimeCompletion prime rank actor values
          (signalizerSpectrum prime rank actor values \ {groupPrime})) factor : Set GroupType) := by
  have generation_large : prime ^ (rank + 1) ≤ Nat.card actor :=
    (pow_le_pow_right' prime_prime.one_le (by omega : rank + 1 ≤ rank + 2)).trans large
  have rank_large : prime ^ rank ≤ Nat.card actor :=
    (pow_le_pow_right' prime_prime.one_le (Nat.le_succ rank)).trans generation_large
  have actor_nontrivial : actor ≠ ⊥ := by
    intro trivial
    have cardinality := (Subgroup.eq_bot_iff_card actor).mp trivial
    rw [cardinality] at large
    have prime_bound : prime ≤ prime ^ (rank + 2) := by
      simpa only [pow_one] using pow_le_pow_right' prime_prime.one_le (by omega : 1 ≤ rank + 2)
    have lower := prime_bound.trans large
    have prime_large := prime_prime.two_le
    omega
  have source_coprime := signalizer_subgroup_coprime prime rank prime_prime actor elementary rank_large
    values conditions.coprime source source_compatible.1 source_compatible.2
  have generation := hyperplane_generation_subtype prime prime_prime actor source elementary actor_nontrivial
    source_compatible.1 source_coprime
  conv_lhs => rw [← generation]
  apply iSup_le
  intro hyperplane
  let complement := signalizerPrimeCompletion prime rank actor values
    (signalizerSpectrum prime rank actor values \ {groupPrime})
  let core := signalizerHyperplaneCore prime rank groupPrime actor hyperplane.val values
  have properties := signalizer_hyperplane_core_properties prime rank groupPrime prime_prime groupPrime_prime
    actor hyperplane.val elementary generation_large values conditions locally_complete prime_member
  have splitting := signalizer_hyperplane_core_splitting prime rank groupPrime prime_prime groupPrime_prime
    actor hyperplane.val source elementary large hyperplane.property.1 hyperplane.property.2 values conditions
    locally_complete prime_member source_compatible.1 local_factorization
  have closure_equal := normalized_conjugate_hull_product complement core (complement ⊓ source) factor
    properties.1 (inf_le_right.trans source_normalizes) splitting
  change source ⊓ Subgroup.centralizer (hyperplane.val : Set GroupType) ≤
    Subgroup.normalizer (normalizedConjugateHull complement factor : Set GroupType)
  rw [closure_equal]
  exact normalized_conjugate_hull_external_normalized _ core factor
    ((signalizer_compatible_hyperplane_fixed_le prime rank actor hyperplane.val source values
      source_compatible).trans properties.2.2) (inf_le_left.trans source_normalizes)

theorem signalizer_local_factorization_complete
    (prime rank groupPrime : ℕ) (prime_prime : prime.Prime) (groupPrime_prime : groupPrime.Prime)
    (actor source factor : Subgroup GroupType) (elementary : IsElemAbelian prime actor)
    (large : prime ^ (rank + 2) ≤ Nat.card actor)
    (values : Subgroup GroupType → Subgroup GroupType)
    (conditions : SolvableSignalizerConditions prime rank actor values)
    (locally_complete : solvableSignalizerLocallyComplete prime rank actor values)
    (prime_member : groupPrime ∈ signalizerSpectrum prime rank actor values)
    (source_compatible : signalizerCompatible prime rank actor values source)
    (factor_compatible : signalizerCompatible prime rank actor values factor)
    (factor_pgroup : IsPGroup groupPrime factor) (abelian : IsMulCommutative factor)
    (factor_nontrivial : factor ≠ ⊥)
    (source_normalizes : source ≤ Subgroup.normalizer (factor : Set GroupType))
    (local_factorization : ∀ selected ∈ signalizerFunctorEk prime rank actor,
      values selected =
        (primeSetCore (GroupType := values selected) ({groupPrime}ᶜ)).map (values selected).subtype ⊔
          (values selected ⊓ source)) :
    solvableSignalizerCompatible prime rank actor values
      (⨆ selected ∈ signalizerFunctorEk prime rank actor, values selected) := by
  have generation_large : prime ^ (rank + 1) ≤ Nat.card actor :=
    (pow_le_pow_right' prime_prime.one_le (by omega : rank + 1 ≤ rank + 2)).trans large
  let complement := signalizerPrimeCompletion prime rank actor values
    (signalizerSpectrum prime rank actor values \ {groupPrime})
  let parent := complement ⊔ factor
  let closure := normalizedConjugateHull complement factor
  have control := locally_complete_prime_deleted_control prime rank prime_prime actor elementary
    generation_large values conditions locally_complete groupPrime prime_member
  have product := signalizer_auxiliary_product prime rank groupPrime prime_prime groupPrime_prime actor source
    factor elementary large values conditions locally_complete prime_member source_compatible.1 factor_compatible
    source_normalizes local_factorization
  have common_normalized := signalizer_factorization_common_normalizes_product prime rank groupPrime
    prime_prime actor source factor elementary generation_large values conditions locally_complete prime_member
    source_compatible.1 source_normalizes local_factorization
  have parent_compatible := restricted_abelian_hall_product_solvable_compatible prime rank groupPrime
    prime_prime groupPrime_prime actor parent factor elementary large values conditions locally_complete
    factor_compatible factor_pgroup abelian factor_nontrivial common_normalized product.1
  have closure_le : closure ≤ parent := normalized_conjugate_hull_le complement factor parent le_sup_right
    ((show complement ≤ parent from le_sup_left).trans Subgroup.le_normalizer)
  have closure_nontrivial : closure ≠ ⊥ := by
    intro trivial
    exact factor_nontrivial (eq_bot_iff.mpr (trivial ▸ subgroup_le_normalized_conjugate_hull complement factor))
  have closure_normalized := normalized_conjugate_hull_external_normalized actor complement factor
    control.1.1.1 factor_compatible.1
  have closure_compatible := solvable_signalizer_compatible_of_le prime rank actor values parent closure
    parent_compatible closure_le closure_normalized
  have normalizer_complete := locally_complete.1 closure closure_nontrivial closure_compatible
  have normalizer_control := signalizer_normalizer_completion_control prime rank prime_prime actor closure
    elementary generation_large values conditions.coprime closure_compatible.1 normalizer_complete.1
  have complement_le := normalizer_control.2.2.2 complement control.1.1
    (normalized_conjugate_hull_normalized complement factor)
  have source_le := normalizer_control.2.2.2 source source_compatible
    (signalizer_factorization_source_normalizes_closure prime rank groupPrime prime_prime groupPrime_prime
      actor source factor elementary large values conditions locally_complete prime_member source_compatible
      source_normalizes local_factorization)
  have completion_le : (⨆ selected ∈ signalizerFunctorEk prime rank actor, values selected) ≤
      signalizerNormalizerCompletion prime rank actor values closure := by
    apply iSup_le
    intro selected
    apply iSup_le
    intro member
    rw [local_factorization selected member]
    exact sup_le ((signalizer_local_complement_core_le_prime_completion prime rank groupPrime prime_prime
      groupPrime_prime actor elementary generation_large values conditions
      (locally_complete.2 groupPrime prime_member).1 selected member).trans complement_le)
      (inf_le_right.trans source_le)
  exact solvable_signalizer_compatible_of_le prime rank actor values _ _
    ⟨normalizer_control.1, normalizer_complete.2⟩ completion_le
    (signalizer_completion_normalized prime rank actor values conditions.normalized)

end CFSG.SignalizerFunctor.Helpers
