module

public import CFSG.LocalAnalysis.SignalizerFunctor.TwoStageCore

public section

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType]

@[expose] def quotientActionPrimeCore (prime : ℕ) (kernel : Subgroup GroupType) [kernel.Normal] :
    Subgroup GroupType :=
  (primeSetCore (GroupType := GroupType ⧸ kernel) {prime}).comap (QuotientGroup.mk' kernel)

theorem quotient_action_prime_core_normal (prime : ℕ) (kernel : Subgroup GroupType)
    [kernel.Normal] : (quotientActionPrimeCore prime kernel).Normal := by
  let := prime_set_core_normal (GroupType := GroupType ⧸ kernel) {prime}
  exact Subgroup.Normal.comap inferInstance (QuotientGroup.mk' kernel)

theorem kernel_le_quotient_action_prime_core (prime : ℕ) (kernel : Subgroup GroupType)
    [kernel.Normal] : kernel ≤ quotientActionPrimeCore prime kernel := by
  unfold quotientActionPrimeCore
  simpa only [QuotientGroup.ker_mk'] using
    Subgroup.ker_le_comap (QuotientGroup.mk' kernel)
      (primeSetCore (GroupType := GroupType ⧸ kernel) {prime})

variable [Finite GroupType]

theorem quotient_action_prime_core_image_pgroup (prime : ℕ) (prime_prime : prime.Prime)
    (kernel : Subgroup GroupType) [kernel.Normal] :
    IsPGroup prime ((quotientActionPrimeCore prime kernel).map (QuotientGroup.mk' kernel)) := by
  unfold quotientActionPrimeCore
  rw [Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective kernel)]
  exact prime_core_isPGroup prime prime_prime

theorem prime_core_le_quotient_action_prime_core (prime : ℕ) (prime_prime : prime.Prime)
    (kernel : Subgroup GroupType) [kernel.Normal] :
    primeSetCore (GroupType := GroupType) {prime} ≤ quotientActionPrimeCore prime kernel := by
  have image_le : (primeSetCore (GroupType := GroupType) {prime}).map (QuotientGroup.mk' kernel) ≤
      primeSetCore (GroupType := GroupType ⧸ kernel) {prime} := by
    apply prime_set_core_contains
    · exact (prime_set_core_normal {prime}).map (QuotientGroup.mk' kernel)
        (QuotientGroup.mk'_surjective kernel)
    · exact (prime_supported_singleton_iff_pgroup prime prime_prime _).mpr
        ((prime_core_isPGroup prime prime_prime).map (QuotientGroup.mk' kernel))
  exact Subgroup.map_le_iff_le_comap.mp image_le

theorem quotient_action_prime_core_pgroup_of_kernel (prime : ℕ) (prime_prime : prime.Prime)
    (kernel : Subgroup GroupType) [kernel.Normal] (kernel_pgroup : IsPGroup prime kernel) :
    IsPGroup prime (quotientActionPrimeCore prime kernel) := by
  apply (prime_core_isPGroup (GroupType := GroupType ⧸ kernel) prime prime_prime).comap_of_ker_isPGroup
    (QuotientGroup.mk' kernel)
  rw [QuotientGroup.ker_mk']
  exact kernel_pgroup

theorem quotient_action_prime_core_eq_prime_core (prime : ℕ) (prime_prime : prime.Prime)
    (kernel : Subgroup GroupType) [kernel.Normal] (kernel_pgroup : IsPGroup prime kernel) :
    quotientActionPrimeCore prime kernel = primeSetCore {prime} := by
  apply le_antisymm
  · exact prime_set_core_contains {prime} _ (quotient_action_prime_core_normal prime kernel)
      ((prime_supported_singleton_iff_pgroup prime prime_prime _).mpr
        (quotient_action_prime_core_pgroup_of_kernel prime prime_prime kernel kernel_pgroup))
  · exact prime_core_le_quotient_action_prime_core prime prime_prime kernel

@[expose] def conjugationActionPrimeCore (prime : ℕ) (base : Subgroup GroupType) [base.Normal] :
    Subgroup GroupType :=
  quotientActionPrimeCore prime (Subgroup.centralizer (base : Set GroupType))

omit [Finite GroupType] in
theorem conjugation_action_prime_core_normal (prime : ℕ) (base : Subgroup GroupType)
    [base.Normal] : (conjugationActionPrimeCore prime base).Normal :=
  quotient_action_prime_core_normal prime _

omit [Finite GroupType] in
theorem centralizer_le_conjugation_action_prime_core (prime : ℕ) (base : Subgroup GroupType)
    [base.Normal] : Subgroup.centralizer (base : Set GroupType) ≤ conjugationActionPrimeCore prime base :=
  kernel_le_quotient_action_prime_core prime _

theorem conjugation_action_prime_core_eq_prime_core (prime : ℕ) (prime_prime : prime.Prime)
    (base : Subgroup GroupType) [base.Normal]
    (centralizer_pgroup : IsPGroup prime (Subgroup.centralizer (base : Set GroupType))) :
    conjugationActionPrimeCore prime base = primeSetCore {prime} :=
  quotient_action_prime_core_eq_prime_core prime prime_prime _ centralizer_pgroup

end CFSG.SignalizerFunctor.Helpers
