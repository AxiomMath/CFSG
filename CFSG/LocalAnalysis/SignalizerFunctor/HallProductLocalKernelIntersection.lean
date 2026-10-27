module

public import CFSG.LocalAnalysis.SignalizerFunctor.AmbientCommutators
public import CFSG.LocalAnalysis.SignalizerFunctor.HallProductLocalCommutators
public import CFSG.LocalAnalysis.SignalizerFunctor.ConjugateIntersections

public section

open CFSG.Open

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]
variable {prime rank groupPrime : ℕ} {actor parent complement factor : Subgroup GroupType}
variable {values : Subgroup GroupType → Subgroup GroupType}

theorem incomplete_hall_product_local_core_le_kernel_intersection (fixedActor selected : Subgroup GroupType)
    (datum : IncompleteSignalizerHallProduct prime rank groupPrime actor parent complement factor values)
    (fixedActor_le : fixedActor ≤ actor) (selected_member : selected ∈ signalizerFunctorEk prime rank actor)
    (selected_le : selected ≤ fixedActor)
    (common_le_parent : signalizerCommonFixed prime rank actor values ≤ parent)
    (complement_eq : complement = signalizerPrimeCompletion prime rank actor values
      (signalizerSpectrum prime rank actor values \ {groupPrime})) :
    let localFixed := parent ⊓ Subgroup.centralizer (fixedActor : Set GroupType)
    let localFactor := factor ⊓ Subgroup.centralizer (fixedActor : Set GroupType)
    (primeSetCore (GroupType := localFixed) ({groupPrime}ᶜ)).map localFixed.subtype ≤
      conjugateIntersection localFactor complement := by
  let localFixed := parent ⊓ Subgroup.centralizer (fixedActor : Set GroupType)
  let internalCore := primeSetCore (GroupType := localFixed) ({groupPrime}ᶜ)
  let localCore := internalCore.map localFixed.subtype
  let localFactor := factor ⊓ Subgroup.centralizer (fixedActor : Set GroupType)
  have contained : localCore ≤ complement := by
    rw [complement_eq]
    exact incomplete_hall_product_local_core_le_prime_completion fixedActor selected datum fixedActor_le
      selected_member selected_le common_le_parent
  let _characteristic := prime_set_core_characteristic (GroupType := localFixed) ({groupPrime}ᶜ)
  have normalized : localFactor ≤ Subgroup.normalizer (localCore : Set GroupType) :=
    (inf_le_inf_right _ datum.factor_le).trans
      (characteristic_subgroup_map_normalized localFixed localFixed Subgroup.le_normalizer internalCore)
  exact normalized_subgroup_le_conjugate_intersection localFactor complement localCore contained normalized

theorem incomplete_hall_product_smaller_local_core_le_kernel_intersection
    (fixedActor smallerFixed selected : Subgroup GroupType)
    (datum : IncompleteSignalizerHallProduct prime rank groupPrime actor parent complement factor values)
    (fixedActor_le : fixedActor ≤ actor) (smaller_le : smallerFixed ≤ fixedActor)
    (selected_member : selected ∈ signalizerFunctorEk prime rank actor) (selected_le : selected ≤ smallerFixed)
    (common_le_parent : signalizerCommonFixed prime rank actor values ≤ parent)
    (complement_eq : complement = signalizerPrimeCompletion prime rank actor values
      (signalizerSpectrum prime rank actor values \ {groupPrime})) :
    let localFixed := parent ⊓ Subgroup.centralizer (smallerFixed : Set GroupType)
    (primeSetCore (GroupType := localFixed) ({groupPrime}ᶜ)).map localFixed.subtype ≤
      conjugateIntersection (factor ⊓ Subgroup.centralizer (fixedActor : Set GroupType)) complement := by
  let localFixed := parent ⊓ Subgroup.centralizer (smallerFixed : Set GroupType)
  let internalCore := primeSetCore (GroupType := localFixed) ({groupPrime}ᶜ)
  let localCore := internalCore.map localFixed.subtype
  have contained : localCore ≤ complement := by
    rw [complement_eq]
    exact incomplete_hall_product_local_core_le_prime_completion smallerFixed selected datum
      (smaller_le.trans fixedActor_le) selected_member selected_le common_le_parent
  let _characteristic := prime_set_core_characteristic (GroupType := localFixed) ({groupPrime}ᶜ)
  have factor_local : factor ⊓ Subgroup.centralizer (fixedActor : Set GroupType) ≤ localFixed :=
    inf_le_inf datum.factor_le (Subgroup.centralizer_le smaller_le)
  have normalized := factor_local.trans
    (characteristic_subgroup_map_normalized localFixed localFixed Subgroup.le_normalizer internalCore)
  exact normalized_subgroup_le_conjugate_intersection _ complement localCore contained normalized

theorem incomplete_hall_product_local_core_commutator_facts (fixedActor target : Subgroup GroupType)
    (datum : IncompleteSignalizerHallProduct prime rank groupPrime actor parent complement factor values)
    (fixedActor_le : fixedActor ≤ actor) (sylowPrime : ℕ)
    (target_pgroup : IsPGroup sylowPrime target)
    (target_le : target ≤
      (primeSetCore (GroupType := (parent ⊓ Subgroup.centralizer (fixedActor : Set GroupType) : Subgroup GroupType))
        ({groupPrime}ᶜ)).map
        (parent ⊓ Subgroup.centralizer (fixedActor : Set GroupType)).subtype)
    (normalized : actor ≤ Subgroup.normalizer (target : Set GroupType))
    (factor_normalized : factor ⊓ Subgroup.centralizer (fixedActor : Set GroupType) ≤
      Subgroup.normalizer (target : Set GroupType)) :
    let localFactor := factor ⊓ Subgroup.centralizer (fixedActor : Set GroupType)
    let commutators : Subgroup GroupType := ⁅target, localFactor⁆
    commutators ≤ target ∧ IsPGroup sylowPrime commutators ∧
      actor ≤ Subgroup.normalizer (commutators : Set GroupType) ∧
      localFactor ≤ Subgroup.normalizer (commutators : Set GroupType) ∧
      ⁅commutators, localFactor⁆ = commutators := by
  let localFixed := parent ⊓ Subgroup.centralizer (fixedActor : Set GroupType)
  let localFactor := factor ⊓ Subgroup.centralizer (fixedActor : Set GroupType)
  let commutators : Subgroup GroupType := ⁅target, localFactor⁆
  change commutators ≤ target ∧ IsPGroup sylowPrime commutators ∧
    actor ≤ Subgroup.normalizer (commutators : Set GroupType) ∧
    localFactor ≤ Subgroup.normalizer (commutators : Set GroupType) ∧ ⁅commutators, localFactor⁆ = commutators
  have contained : commutators ≤ target := commutator_le_of_normalizing target localFactor factor_normalized
  have factor_actor_normalized : actor ≤ Subgroup.normalizer (localFactor : Set GroupType) :=
    normalizer_inf_of_le actor _ _ datum.factor_compatible.1
      ((elementary_abelian_le_centralizer prime actor fixedActor datum.elementary fixedActor_le).trans Subgroup.le_normalizer)
  have commutators_actor_normalized : actor ≤ Subgroup.normalizer (commutators : Set GroupType) := by
    apply Subgroup.le_normalizer_iff.mpr
    intro actorElement actor_member element member
    have target_preserved : conjugateSubgroup actorElement target = target :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (normalized actor_member)
    have factor_preserved : conjugateSubgroup actorElement localFactor = localFactor :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (factor_actor_normalized actor_member)
    have mapped := Subgroup.mem_map_of_mem (MulAut.conj actorElement).toMonoidHom member
    change actorElement * element * actorElement⁻¹ ∈ (⁅target, localFactor⁆ : Subgroup GroupType).map
      (MulAut.conj actorElement).toMonoidHom at mapped
    rw [Subgroup.map_commutator] at mapped
    change actorElement * element * actorElement⁻¹ ∈
      ⁅conjugateSubgroup actorElement target, conjugateSubgroup actorElement localFactor⁆ at mapped
    rw [target_preserved, factor_preserved] at mapped
    exact mapped
  have target_coprime : Nat.Coprime groupPrime (Nat.card target) := by
    apply (prime_supported_complement_singleton_iff_coprime groupPrime datum.groupPrime_prime _).mp
    apply prime_supported_of_dvd ({groupPrime}ᶜ) _ (Subgroup.card_dvd_of_le target_le)
    rw [Subgroup.card_map_of_injective localFixed.subtype_injective]
    exact prime_set_core_supported ({groupPrime}ᶜ)
  exact ⟨contained, target_pgroup.to_le contained, commutators_actor_normalized,
    normalized_commutator_normalized localFactor target factor_normalized,
    coprime_normalized_commutator_idempotent groupPrime datum.groupPrime_prime localFactor target
      (datum.factor_pgroup.to_le inf_le_left) factor_normalized target_coprime⟩

theorem incomplete_abelian_hall_product_local_commutator_le_smaller_core
    (fixedActor smallerFixed selected target : Subgroup GroupType)
    (datum : IncompleteSignalizerHallProduct prime rank groupPrime actor parent complement factor values)
    (abelian : IsMulCommutative factor) (fixedActor_le : fixedActor ≤ actor) (smaller_le : smallerFixed ≤ fixedActor)
    (selected_member : selected ∈ signalizerFunctorEk prime rank actor) (selected_le : selected ≤ smallerFixed)
    (sylowPrime : ℕ) (target_pgroup : IsPGroup sylowPrime target)
    (target_le : target ≤
      (primeSetCore (GroupType := (parent ⊓ Subgroup.centralizer (fixedActor : Set GroupType) : Subgroup GroupType))
        ({groupPrime}ᶜ)).map (parent ⊓ Subgroup.centralizer (fixedActor : Set GroupType)).subtype)
    (normalized : actor ≤ Subgroup.normalizer (target : Set GroupType))
    (factor_normalized : factor ⊓ Subgroup.centralizer (fixedActor : Set GroupType) ≤
      Subgroup.normalizer (target : Set GroupType)) :
    let smallerLocal := parent ⊓ Subgroup.centralizer (smallerFixed : Set GroupType)
    let localFactor := factor ⊓ Subgroup.centralizer (fixedActor : Set GroupType)
    ⁅target, localFactor⁆ ≤ (primeSetCore (GroupType := smallerLocal) ({groupPrime}ᶜ)).map smallerLocal.subtype := by
  let fixedLocal := parent ⊓ Subgroup.centralizer (fixedActor : Set GroupType)
  let smallerLocal := parent ⊓ Subgroup.centralizer (smallerFixed : Set GroupType)
  let localFactor := factor ⊓ Subgroup.centralizer (fixedActor : Set GroupType)
  let commutators : Subgroup GroupType := ⁅target, localFactor⁆
  have facts := incomplete_hall_product_local_core_commutator_facts fixedActor target datum fixedActor_le
    sylowPrime target_pgroup target_le normalized factor_normalized
  have target_fixed : target ≤ fixedLocal := target_le.trans (Subgroup.map_subtype_le _)
  have commutators_smaller : commutators ≤ smallerLocal := facts.1.trans
    (target_fixed.trans (inf_le_inf_left _ (Subgroup.centralizer_le smaller_le)))
  have target_coprime : Nat.Coprime groupPrime (Nat.card target) := by
    apply (prime_supported_complement_singleton_iff_coprime groupPrime datum.groupPrime_prime _).mp
    apply prime_supported_of_dvd ({groupPrime}ᶜ) _ (Subgroup.card_dvd_of_le target_le)
    rw [Subgroup.card_map_of_injective fixedLocal.subtype_injective]
    exact prime_set_core_supported ({groupPrime}ᶜ)
  have commutators_coprime := target_coprime.of_dvd_right (Subgroup.card_dvd_of_le facts.1)
  have absorbed := incomplete_abelian_hall_product_local_commutator_le_core smallerFixed selected localFactor
    commutators datum abelian (smaller_le.trans fixedActor_le) selected_member selected_le
    (inf_le_inf_left _ (Subgroup.centralizer_le smaller_le)) commutators_smaller facts.2.2.2.1 commutators_coprime
  rw [facts.2.2.2.2] at absorbed
  exact absorbed

end CFSG.SignalizerFunctor.Helpers
