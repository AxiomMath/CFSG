module

public import CFSG.LocalAnalysis.SignalizerFunctor.HallProductLocalCentralizers
public import CFSG.LocalAnalysis.SignalizerFunctor.HallProductEscapeInfrastructure
public import CFSG.LocalAnalysis.SignalizerFunctor.HallProductPrimeCompletionEscape

public section

open CFSG.Open

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]
variable {prime rank groupPrime : ℕ} {actor parent complement factor : Subgroup GroupType}
variable {values : Subgroup GroupType → Subgroup GroupType}

theorem incomplete_abelian_hall_product_fixed_core_sylow_escape (kernel : Subgroup GroupType)
    (datum : IncompleteSignalizerHallProduct prime rank groupPrime actor parent complement factor values)
    (abelian : IsMulCommutative factor)
    (common_le_parent : signalizerCommonFixed prime rank actor values ≤ parent)
    (kernel_le : kernel ≤ complement) (kernel_nontrivial : kernel ≠ ⊥)
    (kernel_normal : (kernel.subgroupOf complement).Normal)
    (kernel_normalized : actor ≤ Subgroup.normalizer (kernel : Set GroupType))
    (common_normalized : signalizerCommonFixed prime rank actor values ≤ Subgroup.normalizer (kernel : Set GroupType))
    (kernelPrime : ℕ) (kernelPrime_prime : kernelPrime.Prime)
    (kernelPrime_spectrum : kernelPrime ∈ signalizerSpectrum prime rank actor values)
    (kernelPrime_distinct : kernelPrime ≠ groupPrime) (kernel_coprime : Nat.Coprime kernelPrime (Nat.card kernel)) :
    let common := parent ⊓ Subgroup.centralizer (actor : Set GroupType)
    let core := (primeSetCore (GroupType := common) ({groupPrime}ᶜ)).map common.subtype
    ∀ sylow : Sylow kernelPrime core,
      ¬ (sylow : Subgroup core).map core.subtype ≤ Subgroup.normalizer (factor : Set GroupType) := by
  classical
  let common := parent ⊓ Subgroup.centralizer (actor : Set GroupType)
  let internalCore := primeSetCore (GroupType := common) ({groupPrime}ᶜ)
  let core := internalCore.map common.subtype
  let control := common ⊓ Subgroup.normalizer (factor : Set GroupType)
  let completion := signalizerPrimeCompletion prime rank actor values
    (signalizerSpectrum prime rank actor values \ {kernelPrime})
  change ∀ sylow : Sylow kernelPrime core, ¬ (sylow : Subgroup core).map core.subtype ≤ _
  intro sylow assumed
  have parent_coprime := incomplete_hall_product_parent_coprime datum
  have actor_pgroup := elementary_abelian_isPGroup prime actor datum.elementary
  have rank_large : prime ^ rank ≤ Nat.card actor := by
    apply le_trans _ datum.large
    rw [pow_succ]
    exact Nat.le_mul_of_pos_right _ datum.prime_prime.pos
  obtain ⟨base, base_member⟩ := signalizerFunctorEk_nonempty prime rank datum.prime_prime actor
    datum.elementary rank_large
  have common_product := incomplete_abelian_hall_product_local_normalizer_product actor base datum abelian
    le_rfl base_member base_member.1
  have common_invariant := incomplete_hall_product_local_fixed_normalized actor datum le_rfl
  let _characteristic := prime_set_core_characteristic (GroupType := common) ({groupPrime}ᶜ)
  have core_normalized := characteristic_subgroup_map_normalized actor common common_invariant internalCore
  have core_le_common : core ≤ common := Subgroup.map_subtype_le _
  have common_core_normalized : common ≤ Subgroup.normalizer (core : Set GroupType) :=
    characteristic_subgroup_map_normalized common common Subgroup.le_normalizer internalCore
  have sylow_control : (sylow : Subgroup core).map core.subtype ≤ control :=
    le_inf ((Subgroup.map_subtype_le _).trans core_le_common) assumed
  have deleted_complete := datum.locally_complete.2 kernelPrime kernelPrime_spectrum
  have completion_control := signalizer_prime_completion_control prime rank datum.prime_prime actor
    datum.elementary datum.large values datum.conditions _ deleted_complete.1
  have factor_completion : factor ≤ completion := by
    rw [← elementary_abelian_centralizer_generation prime rank datum.prime_prime actor factor datum.elementary
      datum.large datum.factor_compatible.1 (parent_coprime.of_dvd_right (Subgroup.card_dvd_of_le datum.factor_le))]
    apply iSup_le
    intro selected
    apply iSup_le
    intro selected_member
    let localFixed := parent ⊓ Subgroup.centralizer (selected : Set GroupType)
    let localFactor := factor ⊓ Subgroup.centralizer (selected : Set GroupType)
    have localFactor_le : localFactor ≤ localFixed := inf_le_inf_right _ datum.factor_le
    have localFixed_normalized := incomplete_hall_product_local_fixed_normalized selected datum selected_member.1
    have localFactor_normalized := normalizer_inf_of_le actor factor
      (Subgroup.centralizer (selected : Set GroupType)) datum.factor_compatible.1
      ((elementary_abelian_le_centralizer prime actor selected datum.elementary selected_member.1).trans Subgroup.le_normalizer)
    have local_solvable := incomplete_hall_product_local_fixed_solvable selected selected datum selected_member le_rfl
    have localFactor_supported : primeSupported ({kernelPrime}ᶜ) (Nat.card localFactor) := by
      intro divisor divisor_prime divides same
      have equal := (prime_supported_singleton_iff_pgroup groupPrime datum.groupPrime_prime localFactor).mpr
        (datum.factor_pgroup.to_le inf_le_left) divisor divisor_prime divides
      exact kernelPrime_distinct (same.symm.trans equal)
    obtain ⟨hall, localFactor_hall, hall_local, hall_property, hall_normalized⟩ :=
      normalized_invariant_hall_containing prime datum.prime_prime actor localFixed localFactor actor_pgroup
        local_solvable (parent_coprime.of_dvd_right (Subgroup.card_dvd_of_le inf_le_left)) localFixed_normalized
        localFactor_le localFactor_normalized ({kernelPrime}ᶜ) localFactor_supported
    have common_le_local : common ≤ localFixed := inf_le_inf_left _ (Subgroup.centralizer_le selected_member.1)
    have normalized_intersection := normalized_hall_intersection prime datum.prime_prime actor localFixed hall core
      actor_pgroup local_solvable (parent_coprime.of_dvd_right (Subgroup.card_dvd_of_le inf_le_left))
      localFixed_normalized hall_normalized core_normalized (core_le_common.trans common_le_local)
      ({kernelPrime}ᶜ) hall_property (by
        intro element member
        exact common_core_normalized ⟨member.1.1, member.2⟩)
    let intersection := hall ⊓ core
    have intersection_hall : IsHallSubgroup ({kernelPrime}ᶜ) (intersection.subgroupOf core) := by
      have equal : intersection.subgroupOf core = hall.subgroupOf core := by
        ext element
        exact and_iff_left element.property
      rwa [equal]
    have core_product := hall_prime_complement_sylow_product kernelPrime kernelPrime_prime core intersection
      inf_le_right intersection_hall sylow
    have replacement := subgroup_product_replace_contained_factor common core control intersection
      ((sylow : Subgroup core).map core.subtype) core_le_common inf_le_left inf_le_right sylow_control
      common_product core_product
    have control_normalizes : control ≤ Subgroup.normalizer (localFactor : Set GroupType) :=
      normalizer_inf_of_le control factor (Subgroup.centralizer (selected : Set GroupType)) inf_le_right
        ((inf_le_left.trans inf_le_right).trans
          ((Subgroup.centralizer_le selected_member.1).trans Subgroup.le_normalizer))
    let orbit := normalizedConjugateHull common localFactor
    have orbit_hall : orbit ≤ hall := normalized_orbit_le_of_product common localFactor hall intersection control
      replacement inf_le_left localFactor_hall control_normalizes
    have orbit_normalized : actor ≤ Subgroup.normalizer (orbit : Set GroupType) :=
      normalized_conjugate_hull_external_normalized actor common localFactor common_invariant localFactor_normalized
    have orbit_compatible := incomplete_hall_product_normalized_compatible orbit datum
      (orbit_hall.trans (hall_local.trans inf_le_left)) orbit_normalized
    have orbit_supported : primeSupported (signalizerSpectrum prime rank actor values \ {kernelPrime})
        (Nat.card orbit) := by
      intro divisor divisor_prime divides
      obtain ⟨fixedSelected, member, value_divides⟩ := signalizer_compatible_prime_support prime rank divisor
        datum.prime_prime divisor_prime actor datum.elementary datum.large values datum.conditions.coprime
        orbit orbit_compatible divides
      refine ⟨⟨divisor_prime, fixedSelected, member, value_divides⟩, ?_⟩
      have hall_supported : primeSupported ({kernelPrime}ᶜ) (Nat.card hall) := by
        have supported := hall_property.1
        rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hall_local).toEquiv] at supported
      exact hall_supported divisor divisor_prime (divides.trans (Subgroup.card_dvd_of_le orbit_hall))
    have orbit_common : signalizerCommonFixed prime rank actor values ≤ Subgroup.normalizer (orbit : Set GroupType) := by
      rw [incomplete_hall_product_common_fixed_eq datum common_le_parent]
      exact normalized_conjugate_hull_normalized common localFactor
    exact (subgroup_le_normalized_conjugate_hull common localFactor).trans
      (completion_control.2.2.2 orbit orbit_compatible orbit_supported orbit_common)
  exact incomplete_abelian_hall_product_prime_completion_escape kernel datum abelian kernel_le kernel_nontrivial
    kernel_normal kernel_normalized common_normalized kernelPrime kernelPrime_prime kernelPrime_spectrum kernel_coprime
    factor_completion

end CFSG.SignalizerFunctor.Helpers
