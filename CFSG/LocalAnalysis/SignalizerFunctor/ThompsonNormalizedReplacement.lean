module

public import CFSG.LocalAnalysis.SignalizerFunctor.PrimeTransitivity
public import CFSG.LocalAnalysis.SignalizerFunctor.AbelianReplacementAbelianness
public import CFSG.LocalAnalysis.SignalizerFunctor.AbelianReplacementConjugator
public import CFSG.LocalAnalysis.SignalizerFunctor.AbelianReplacementGrowth

public section

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]

theorem maximum_order_abelian_normalized_replacement
    (prime : ℕ) (prime_prime : prime.Prime) (odd_prime : prime ≠ 2)
    (pgroup : IsPGroup prime GroupType) (normal : Subgroup GroupType) [normal.Normal]
    (class_two : ⁅normal, normal⁆ ≤ Subgroup.centralizer (normal : Set GroupType))
    (derived_le : ⁅normal, normal⁆ ≤ orderThompsonCenter GroupType)
    (witness : Subgroup GroupType) (witness_member : witness ∈ maximumOrderAbelianFamily GroupType)
    (witness_omits : ¬ normal ≤ witness) :
    ∃ target ∈ maximumOrderAbelianFamily GroupType,
      ¬ normal ≤ target ∧ normal ≤ Subgroup.normalizer (target : Set GroupType) := by
  classical
  let candidates := {target : Subgroup GroupType //
    target ∈ maximumOrderAbelianFamily GroupType ∧ ¬ normal ≤ target}
  let _nonempty : Nonempty candidates := ⟨⟨witness, witness_member, witness_omits⟩⟩
  let weight := fun candidate : candidates => Nat.card
    (normal ⊓ Subgroup.normalizer (candidate.val : Set GroupType) : Subgroup GroupType)
  obtain ⟨candidate, optimal⟩ := Finite.exists_max weight
  refine ⟨candidate.val, candidate.property.1, candidate.property.2, ?_⟩
  by_contra not_normalized
  obtain ⟨conjugator, member, outside, normalizes⟩ := pgroup_replacement_conjugator_exists prime prime_prime
    pgroup candidate.val normal not_normalized
  have candidate_derived : ⁅normal, normal⁆ ≤ candidate.val := by
    have center_le : orderThompsonCenter GroupType ≤ candidate.val := by
      rw [order_thompson_center_eq_intersection]
      exact iInf_le_of_le candidate.val (iInf_le_of_le candidate.property.1 le_rfl)
    exact derived_le.trans center_le
  let replacement := abelianReplacement candidate.val conjugator
  have replacement_abelian := abelian_replacement_abelian prime prime_prime odd_prime candidate.val normal
    (pgroup.to_subgroup normal) candidate.property.1.1 class_two candidate_derived conjugator member normalizes
  have replacement_card := abelian_replacement_card candidate.val normal candidate_derived conjugator member
    candidate.property.1.1 normalizes
  have replacement_member : replacement ∈ maximumOrderAbelianFamily GroupType := by
    refine ⟨replacement_abelian, ?_⟩
    intro target abelian
    rw [replacement_card]
    exact candidate.property.1.2 target abelian
  have replacement_omits : ¬ normal ≤ replacement := by
    have control := normalizer_conjugate_abelian_product_control candidate.val candidate.property.1.1
      conjugator normalizes
    have replacement_le : replacement ≤ Subgroup.normalizer (candidate.val : Set GroupType) :=
      (sup_le (inf_le_left.trans le_sup_left)
        (abelian_replacement_difference_le_product candidate.val conjugator)).trans control.1
    intro contained
    exact outside (replacement_le (contained member))
  have growth := abelian_replacement_strict_normalizer_growth candidate.val normal candidate_derived
    candidate.property.1.1 conjugator member outside normalizes
  have cardinal_growth := subgroup_card_strict_mono growth
  have bound := optimal (⟨replacement, replacement_member, replacement_omits⟩ : candidates)
  exact (not_lt_of_ge bound) cardinal_growth

end CFSG.SignalizerFunctor.Helpers
