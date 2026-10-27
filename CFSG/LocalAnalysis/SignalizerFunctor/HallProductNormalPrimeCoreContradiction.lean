module

public import CFSG.LocalAnalysis.SignalizerFunctor.HallProductKernelIntersection
public import CFSG.LocalAnalysis.SignalizerFunctor.HallProductWeakClosureContradiction

public section

open CFSG.Open

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]
variable {prime rank groupPrime : ℕ} {actor parent complement factor : Subgroup GroupType}
variable {values : Subgroup GroupType → Subgroup GroupType}

theorem incomplete_abelian_hall_product_normal_prime_kernel_contradiction (kernel : Subgroup GroupType)
    (datum : IncompleteSignalizerHallProduct prime rank groupPrime actor parent complement factor values)
    (abelian : IsMulCommutative factor) (large : prime ^ (rank + 2) ≤ Nat.card actor)
    (common_le_parent : signalizerCommonFixed prime rank actor values ≤ parent)
    (complement_eq : complement = signalizerPrimeCompletion prime rank actor values
      (signalizerSpectrum prime rank actor values \ {groupPrime}))
    (kernel_le : kernel ≤ complement) (kernel_nontrivial : kernel ≠ ⊥)
    (kernel_normal : (kernel.subgroupOf complement).Normal)
    (kernel_normalized : actor ≤ Subgroup.normalizer (kernel : Set GroupType))
    (common_normalized : signalizerCommonFixed prime rank actor values ≤ Subgroup.normalizer (kernel : Set GroupType))
    (kernelPrime : ℕ) (kernelPrime_prime : kernelPrime.Prime) (kernel_pgroup : IsPGroup kernelPrime kernel)
    (witnessPrime : ℕ) (witnessPrime_prime : witnessPrime.Prime) (witnessPrime_divides : witnessPrime ∣ Nat.card complement)
    (distinct : witnessPrime ≠ kernelPrime) : False := by
  have kernel_distinct : kernelPrime ≠ groupPrime := by
    intro equal
    have kernel_coprime := datum.complement_coprime.of_dvd_right (Subgroup.card_dvd_of_le kernel_le)
    let : Fact kernelPrime.Prime := ⟨kernelPrime_prime⟩
    rcases kernel_pgroup.card_eq_or_dvd with cardinality | divides
    · exact kernel_nontrivial ((Subgroup.eq_bot_iff_card _).mpr cardinality)
    · exact datum.groupPrime_prime.coprime_iff_not_dvd.mp kernel_coprime (equal ▸ divides)
  have witness_distinct : witnessPrime ≠ groupPrime := fun equal =>
    datum.groupPrime_prime.coprime_iff_not_dvd.mp datum.complement_coprime (equal ▸ witnessPrime_divides)
  obtain ⟨selected, member, value_divides⟩ := signalizer_compatible_prime_support prime rank witnessPrime datum.prime_prime
    witnessPrime_prime actor datum.elementary datum.large values datum.conditions.coprime complement
    datum.complement_compatible.1 witnessPrime_divides
  have kernel_coprime := prime_coprime_pgroup_card witnessPrime kernelPrime witnessPrime_prime kernelPrime_prime distinct kernel_pgroup
  apply incomplete_abelian_hall_product_weak_closure_contradiction kernel datum abelian large kernelPrime kernelPrime_prime
    kernel_distinct kernel_le kernel_nontrivial kernel_pgroup kernel_normal kernel_normalized
  intro fixedActor fixedActor_member local_nontrivial
  exact incomplete_abelian_hall_product_kernel_intersection fixedActor kernel datum abelian fixedActor_member.1
    fixedActor_member.2.ge common_le_parent complement_eq local_nontrivial kernel_le kernel_nontrivial kernel_normal
    kernel_normalized common_normalized witnessPrime witnessPrime_prime
    ⟨witnessPrime_prime, selected, member, value_divides⟩ witness_distinct kernel_coprime

theorem incomplete_abelian_hall_product_prime_core_contradiction
    (datum : IncompleteSignalizerHallProduct prime rank groupPrime actor parent complement factor values)
    (abelian : IsMulCommutative factor) (large : prime ^ (rank + 2) ≤ Nat.card actor)
    (common_le_parent : signalizerCommonFixed prime rank actor values ≤ parent)
    (complement_eq : complement = signalizerPrimeCompletion prime rank actor values
      (signalizerSpectrum prime rank actor values \ {groupPrime}))
    (kernelPrime witnessPrime : ℕ) (kernelPrime_prime : kernelPrime.Prime) (witnessPrime_prime : witnessPrime.Prime)
    (nontrivial : primeSetCore (GroupType := complement) {kernelPrime} ≠ ⊥)
    (witnessPrime_divides : witnessPrime ∣ Nat.card complement) (distinct : witnessPrime ≠ kernelPrime) : False := by
  let internalKernel := primeSetCore (GroupType := complement) {kernelPrime}
  let kernel := internalKernel.map complement.subtype
  have kernel_le : kernel ≤ complement := Subgroup.map_subtype_le _
  have kernel_nontrivial : kernel ≠ ⊥ := fun trivial => nontrivial
    ((Subgroup.map_eq_bot_iff_of_injective _ complement.subtype_injective).mp trivial)
  let _characteristic := prime_set_core_characteristic (GroupType := complement) {kernelPrime}
  have kernel_normal : (kernel.subgroupOf complement).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer kernel_le).mpr
      (characteristic_subgroup_map_normalized complement complement Subgroup.le_normalizer internalKernel)
  have normalized := characteristic_subgroup_map_normalized actor complement datum.complement_compatible.1.1 internalKernel
  have common_complement : signalizerCommonFixed prime rank actor values ≤ Subgroup.normalizer (complement : Set GroupType) := by
    rw [complement_eq]
    exact (signalizer_prime_completion_control prime rank datum.prime_prime actor datum.elementary datum.large values
      datum.conditions _ (datum.locally_complete.2 groupPrime (incomplete_hall_product_factor_prime_in_spectrum datum)).1).2.2.1
  have common_normalized := characteristic_subgroup_map_normalized _ complement common_complement internalKernel
  exact incomplete_abelian_hall_product_normal_prime_kernel_contradiction kernel datum abelian large common_le_parent
    complement_eq kernel_le kernel_nontrivial kernel_normal normalized common_normalized kernelPrime kernelPrime_prime
    ((prime_core_isPGroup kernelPrime kernelPrime_prime).map complement.subtype) witnessPrime witnessPrime_prime
    witnessPrime_divides distinct

end CFSG.SignalizerFunctor.Helpers
