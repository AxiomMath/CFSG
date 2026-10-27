module

public import CFSG.LocalAnalysis.SignalizerFunctor.FixedGrowth
public import CFSG.LocalAnalysis.SignalizerFunctor.PGroupFixedQuotientEscape

public section

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]

theorem pgroup_replacement_conjugator_exists
    (prime : ℕ) (prime_prime : prime.Prime) (pgroup : IsPGroup prime GroupType)
    (target normal : Subgroup GroupType) [normal.Normal]
    (not_normalized : ¬ normal ≤ Subgroup.normalizer (target : Set GroupType)) :
    ∃ conjugator ∈ normal, conjugator ∉ Subgroup.normalizer (target : Set GroupType) ∧
      conjugator ∈ Subgroup.normalizer (Subgroup.normalizer (target : Set GroupType) : Set GroupType) := by
  let actor := Subgroup.normalizer (target : Set GroupType)
  let kernel := normal ⊓ actor
  let base := normal ⊓ Subgroup.normalizer (kernel : Set GroupType)
  have kernel_proper : kernel < normal := lt_of_le_of_ne inf_le_left (by
    intro equality
    exact not_normalized (equality.symm.le.trans inf_le_right))
  have growth : kernel < base := pgroup_normalizer_strict_growth prime prime_prime normal kernel
    (pgroup.to_subgroup normal) kernel_proper
  have kernel_normalized : actor ≤ Subgroup.normalizer (kernel : Set GroupType) :=
    normalizer_inf_of_le actor normal actor Subgroup.le_normalizer_of_normal Subgroup.le_normalizer
  have base_normalized : actor ≤ Subgroup.normalizer (base : Set GroupType) :=
    normalizer_inf_of_le actor normal _ Subgroup.le_normalizer_of_normal
      (normalizer_normalized actor kernel kernel_normalized)
  have kernel_normal : (kernel.subgroupOf base).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer growth.le).mpr inf_le_right
  obtain ⟨conjugator, conjugator_base, conjugator_outside, fixed⟩ := pgroup_fixed_quotient_escape prime
    prime_prime actor base kernel (pgroup.to_subgroup actor) (pgroup.to_subgroup base) base_normalized
    kernel_normal kernel_normalized growth
  have conjugator_not_actor : conjugator ∉ actor := by
    intro member
    exact conjugator_outside ⟨conjugator_base.1, member⟩
  have conjugated_le : conjugateSubgroup conjugator⁻¹ actor ≤ actor := by
    rintro _ ⟨element, member, rfl⟩
    have difference_member := (fixed (⟨element, member⟩ : actor)).2
    have product := actor.mul_mem difference_member member
    change conjugator⁻¹ * element * (conjugator⁻¹)⁻¹ ∈ actor
    simpa only [conjugationDifference, inv_inv, mul_assoc, inv_mul_cancel, mul_one] using product
  have conjugated_eq : conjugateSubgroup conjugator⁻¹ actor = actor :=
    Subgroup.eq_of_le_of_card_ge conjugated_le (by rw [conjugate_subgroup_card])
  have inverse_normalizes : conjugator⁻¹ ∈ Subgroup.normalizer (actor : Set GroupType) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr conjugated_eq
  refine ⟨conjugator, conjugator_base.1, conjugator_not_actor, ?_⟩
  simpa only [inv_inv] using (Subgroup.normalizer (actor : Set GroupType)).inv_mem inverse_normalizes

end CFSG.SignalizerFunctor.Helpers
