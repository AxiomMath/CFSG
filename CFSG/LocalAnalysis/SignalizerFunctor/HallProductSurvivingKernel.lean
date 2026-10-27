module

public import CFSG.LocalAnalysis.SignalizerFunctor.AmbientFixedCommutators
public import CFSG.LocalAnalysis.SignalizerFunctor.HallProductLocalKernelIntersection
public import CFSG.LocalAnalysis.SignalizerFunctor.HallProductCentralizerTrap
public import CFSG.LocalAnalysis.SignalizerFunctor.CommutatorExtension

public section

open CFSG.Open

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType]

theorem commutator_le_normal_overgroup (parent normal first second : Subgroup GroupType)
    (normal_le : normal ≤ parent) (normal_internal : (normal.subgroupOf parent).Normal)
    (first_le : first ≤ parent) (second_le : second ≤ normal) : ⁅first, second⁆ ≤ normal := by
  have normalized : first ≤ Subgroup.normalizer (normal : Set GroupType) := first_le.trans
    ((Subgroup.normal_subgroupOf_iff_le_normalizer normal_le).mp normal_internal)
  apply (Subgroup.commutator_mono le_rfl second_le).trans
  rw [Subgroup.commutator_comm]
  exact commutator_le_of_normalizing normal first normalized

variable [Finite GroupType]
variable {prime rank groupPrime : ℕ} {actor parent complement factor : Subgroup GroupType}
variable {values : Subgroup GroupType → Subgroup GroupType}

theorem incomplete_abelian_hall_product_surviving_kernel_le_intersection
    (fixedActor witness kernel : Subgroup GroupType)
    (datum : IncompleteSignalizerHallProduct prime rank groupPrime actor parent complement factor values)
    (abelian : IsMulCommutative factor) (fixedActor_le : fixedActor ≤ actor)
    (fixedActor_large : prime ^ (rank + 1) ≤ Nat.card fixedActor)
    (common_le_parent : signalizerCommonFixed prime rank actor values ≤ parent)
    (complement_eq : complement = signalizerPrimeCompletion prime rank actor values
      (signalizerSpectrum prime rank actor values \ {groupPrime}))
    (witnessPrime : ℕ) (witnessPrime_prime : witnessPrime.Prime) (witness_pgroup : IsPGroup witnessPrime witness)
    (witness_le : witness ≤
      (primeSetCore (GroupType := (parent ⊓ Subgroup.centralizer (fixedActor : Set GroupType) : Subgroup GroupType))
        ({groupPrime}ᶜ)).map (parent ⊓ Subgroup.centralizer (fixedActor : Set GroupType)).subtype)
    (witness_normalized : actor ≤ Subgroup.normalizer (witness : Set GroupType))
    (factor_normalized : factor ⊓ Subgroup.centralizer (fixedActor : Set GroupType) ≤
      Subgroup.normalizer (witness : Set GroupType))
    (localFactor_nontrivial : factor ⊓ Subgroup.centralizer (fixedActor : Set GroupType) ≠ ⊥)
    (commutator_nontrivial : (⁅witness, factor ⊓ Subgroup.centralizer (fixedActor : Set GroupType)⁆ : Subgroup GroupType) ≠ ⊥)
    (kernel_le : kernel ≤ complement) (kernel_normal : (kernel.subgroupOf complement).Normal)
    (kernel_normalized : actor ≤ Subgroup.normalizer (kernel : Set GroupType))
    (kernel_coprime : Nat.Coprime witnessPrime (Nat.card kernel)) :
    kernel ≤ conjugateIntersection (factor ⊓ Subgroup.centralizer (fixedActor : Set GroupType)) complement := by
  classical
  let localFixed := parent ⊓ Subgroup.centralizer (fixedActor : Set GroupType)
  let localFactor := factor ⊓ Subgroup.centralizer (fixedActor : Set GroupType)
  let commutators : Subgroup GroupType := ⁅witness, localFactor⁆
  let intersection := conjugateIntersection localFactor complement
  have fixed_elementary := elementary_abelian_of_le prime datum.elementary fixedActor_le
  have fixed_rank : prime ^ rank ≤ Nat.card fixedActor := by
    apply le_trans _ fixedActor_large
    rw [pow_succ]
    exact Nat.le_mul_of_pos_right _ datum.prime_prime.pos
  obtain ⟨selected, selected_member⟩ := signalizerFunctorEk_nonempty prime rank datum.prime_prime fixedActor
    fixed_elementary fixed_rank
  have selected_global : selected ∈ signalizerFunctorEk prime rank actor :=
    ⟨selected_member.1.trans fixedActor_le, selected_member.2⟩
  have facts := incomplete_hall_product_local_core_commutator_facts fixedActor witness datum fixedActor_le
    witnessPrime witness_pgroup witness_le witness_normalized factor_normalized
  have witness_fixed : witness ≤ localFixed := witness_le.trans (Subgroup.map_subtype_le _)
  have commutators_fixed : commutators ≤ localFixed := facts.1.trans witness_fixed
  have localCore_intersection := incomplete_hall_product_local_core_le_kernel_intersection fixedActor selected datum
    fixedActor_le selected_global selected_member.1 common_le_parent complement_eq
  have commutators_intersection : commutators ≤ intersection := facts.1.trans (witness_le.trans localCore_intersection)
  have commutators_kernel_normalizes : commutators ≤ Subgroup.normalizer (kernel : Set GroupType) :=
    (commutators_intersection.trans (conjugate_intersection_le localFactor complement)).trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer kernel_le).mp kernel_normal)
  have kernel_solvable : Group.IsSolvable kernel := by
    let := datum.complement_compatible.2
    exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective kernel_le)
  have kernel_prime_coprime : Nat.Coprime prime (Nat.card kernel) :=
    (incomplete_hall_product_parent_coprime datum).of_dvd_right
      (Subgroup.card_dvd_of_le (kernel_le.trans datum.complement_le))
  have localFactor_actor_normalized : actor ≤ Subgroup.normalizer (localFactor : Set GroupType) :=
    normalizer_inf_of_le actor _ _ datum.factor_compatible.1
      ((elementary_abelian_le_centralizer prime actor fixedActor datum.elementary fixedActor_le).trans Subgroup.le_normalizer)
  have commutators_coprime : Nat.Coprime groupPrime (Nat.card commutators) := by
    apply (prime_supported_complement_singleton_iff_coprime groupPrime datum.groupPrime_prime _).mp
    apply prime_supported_of_dvd ({groupPrime}ᶜ) _ (Subgroup.card_dvd_of_le (facts.1.trans witness_le))
    rw [Subgroup.card_map_of_injective localFixed.subtype_injective]
    exact prime_set_core_supported ({groupPrime}ᶜ)
  have smallerCore_intersection : ∀ smaller ∈ signalizerFunctorEk prime rank fixedActor,
      (primeSetCore (GroupType := (parent ⊓ Subgroup.centralizer (smaller : Set GroupType) : Subgroup GroupType))
        ({groupPrime}ᶜ)).map (parent ⊓ Subgroup.centralizer (smaller : Set GroupType)).subtype ≤ intersection := by
    intro smaller member
    exact incomplete_hall_product_smaller_local_core_le_kernel_intersection fixedActor smaller smaller datum fixedActor_le
      member.1 ⟨member.1.trans fixedActor_le, member.2⟩ le_rfl common_le_parent complement_eq
  have commutators_smallerCore : ∀ smaller ∈ signalizerFunctorEk prime rank fixedActor,
      commutators ≤
      (primeSetCore (GroupType := (parent ⊓ Subgroup.centralizer (smaller : Set GroupType) : Subgroup GroupType))
        ({groupPrime}ᶜ)).map (parent ⊓ Subgroup.centralizer (smaller : Set GroupType)).subtype := by
    intro smaller member
    exact incomplete_abelian_hall_product_local_commutator_le_smaller_core fixedActor smaller smaller witness datum
      abelian fixedActor_le member.1 ⟨member.1.trans fixedActor_le, member.2⟩ le_rfl witnessPrime witness_pgroup witness_le
      witness_normalized factor_normalized
  have mixed_commutator_le : ⁅kernel, commutators⁆ ≤ intersection := by
    rw [solvable_normalized_order_fixed_commutator_generation prime rank witnessPrime datum.prime_prime witnessPrime_prime
      fixedActor commutators kernel fixed_elementary fixedActor_large facts.2.1 kernel_solvable
      (fixedActor_le.trans kernel_normalized) commutators_kernel_normalizes
      (Subgroup.le_centralizer_iff.mpr (commutators_fixed.trans inf_le_right)) kernel_prime_coprime kernel_coprime]
    apply iSup_le
    intro smaller
    apply iSup_le
    intro member
    let smallerLocal := parent ⊓ Subgroup.centralizer (smaller : Set GroupType)
    let internalCore := primeSetCore (GroupType := smallerLocal) ({groupPrime}ᶜ)
    let localCore := internalCore.map smallerLocal.subtype
    have core_normal : (localCore.subgroupOf smallerLocal).Normal := by
      have equal : localCore.subgroupOf smallerLocal = internalCore :=
        Subgroup.comap_map_eq_self_of_injective smallerLocal.subtype_injective internalCore
      rw [equal]
      exact prime_set_core_normal ({groupPrime}ᶜ)
    have contained : kernel ⊓ Subgroup.centralizer (smaller : Set GroupType) ≤ smallerLocal :=
      inf_le_inf_right _ (kernel_le.trans datum.complement_le)
    exact (commutator_le_normal_overgroup smallerLocal localCore _ commutators (Subgroup.map_subtype_le _)
      core_normal contained (commutators_smallerCore smaller member)).trans (smallerCore_intersection smaller member)
  let fixedKernel := kernel ⊓ Subgroup.centralizer (commutators : Set GroupType)
  have fixedKernel_normalized : actor ≤ Subgroup.normalizer (fixedKernel : Set GroupType) :=
    normalizer_inf_of_le actor _ _ kernel_normalized (normalizer_normalizes_centralizer actor commutators facts.2.2.1)
  have fixedKernel_coprime : Nat.Coprime prime (Nat.card fixedKernel) :=
    kernel_prime_coprime.of_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
  have fixedKernel_le : fixedKernel ≤ intersection := by
    rw [← elementary_abelian_centralizer_generation prime rank datum.prime_prime fixedActor fixedKernel fixed_elementary
      fixedActor_large (fixedActor_le.trans fixedKernel_normalized) fixedKernel_coprime]
    apply iSup_le
    intro smaller
    apply iSup_le
    intro member
    let smallerLocal := parent ⊓ Subgroup.centralizer (smaller : Set GroupType)
    let centralizer := smallerLocal ⊓ Subgroup.centralizer (commutators : Set GroupType)
    have smallerLocal_normalized := incomplete_hall_product_local_fixed_normalized smaller datum (member.1.trans fixedActor_le)
    have centralizer_normalized : actor ≤ Subgroup.normalizer (centralizer : Set GroupType) :=
      normalizer_inf_of_le actor _ _ smallerLocal_normalized (normalizer_normalizes_centralizer actor commutators facts.2.2.1)
    have localFactor_centralizes_smaller : localFactor ≤ Subgroup.centralizer (smaller : Set GroupType) :=
      inf_le_right.trans (Subgroup.centralizer_le member.1)
    have localFactor_normalizes_centralizer : localFactor ≤ Subgroup.normalizer (centralizer : Set GroupType) :=
      normalizer_inf_of_le localFactor _ _
        (normalizer_inf_of_le localFactor _ _ ((inf_le_left.trans datum.factor_le).trans Subgroup.le_normalizer)
          (localFactor_centralizes_smaller.trans Subgroup.le_normalizer))
        (normalizer_normalizes_centralizer localFactor commutators facts.2.2.2.1)
    have commutators_centralizes : commutators ≤ Subgroup.centralizer (centralizer : Set GroupType) :=
      Subgroup.le_centralizer_iff.mpr inf_le_right
    have centralizer_coprime := incomplete_abelian_hall_product_commutator_centralizer_coprime localFactor commutators
      centralizer datum abelian inf_le_left localFactor_nontrivial (commutators_fixed.trans inf_le_left) commutators_coprime
      commutator_nontrivial facts.2.2.2.2 facts.2.2.2.1 (inf_le_left.trans inf_le_left) centralizer_normalized
      localFactor_actor_normalized localFactor_normalizes_centralizer commutators_centralizes
    let differences : Subgroup GroupType := ⁅centralizer, localFactor⁆
    have differences_core := incomplete_abelian_hall_product_local_commutator_le_core smaller smaller localFactor centralizer
      datum abelian (member.1.trans fixedActor_le) ⟨member.1.trans fixedActor_le, member.2⟩ le_rfl
      (le_inf inf_le_left localFactor_centralizes_smaller) inf_le_left localFactor_normalizes_centralizer centralizer_coprime
    have differences_intersection : differences ≤ intersection := differences_core.trans (smallerCore_intersection smaller member)
    let combined := (centralizer ⊓ kernel) ⊔ differences
    have combined_normalized : localFactor ≤ Subgroup.normalizer (combined : Set GroupType) :=
      commutator_extension_normalized localFactor centralizer (centralizer ⊓ kernel) localFactor_normalizes_centralizer inf_le_left
    have combined_complement : combined ≤ complement := sup_le (inf_le_right.trans kernel_le)
      (differences_intersection.trans (conjugate_intersection_le localFactor complement))
    have combined_intersection := normalized_subgroup_le_conjugate_intersection localFactor complement combined
      combined_complement combined_normalized
    apply le_trans _ (le_sup_left.trans combined_intersection)
    intro element element_member
    exact ⟨⟨⟨kernel_le.trans datum.complement_le element_member.1.1, element_member.2⟩, element_member.1.2⟩,
      element_member.1.1⟩
  have factorization := coprime_normalized_commutator_factorization witnessPrime witnessPrime_prime commutators kernel
    facts.2.1 commutators_kernel_normalizes kernel_coprime
  exact factorization.symm.le.trans (sup_le mixed_commutator_le fixedKernel_le)

end CFSG.SignalizerFunctor.Helpers
