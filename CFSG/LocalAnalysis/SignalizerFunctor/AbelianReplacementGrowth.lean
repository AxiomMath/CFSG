module

public import CFSG.LocalAnalysis.SignalizerFunctor.AbelianReplacementCardinality

public section

open scoped commutatorElement

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType]

theorem abelian_replacement_contains_derived (target normal : Subgroup GroupType)
    (derived_le : ⁅normal, normal⁆ ≤ target) (conjugator : GroupType) (member : conjugator ∈ normal) :
    ⁅normal, normal⁆ ≤ abelianReplacementIntersection target conjugator :=
  (le_inf derived_le (Subgroup.commutator_le_self normal)).trans
    (abelian_replacement_intersection_contains_normal target normal derived_le conjugator member)

theorem abelian_replacement_old_normalizer_normalizes (target normal : Subgroup GroupType) [normal.Normal]
    (derived_le : ⁅normal, normal⁆ ≤ target) (abelian : IsMulCommutative target)
    (conjugator : GroupType) (member : conjugator ∈ normal)
    (normalizes : conjugator ∈ Subgroup.normalizer
      (Subgroup.normalizer (target : Set GroupType) : Set GroupType)) :
    Subgroup.normalizer (target : Set GroupType) ≤
      Subgroup.normalizer (abelianReplacement target conjugator : Set GroupType) := by
  have control := normalizer_conjugate_target_control target conjugator normalizes
  have product_control := normalizer_conjugate_abelian_product_control target abelian conjugator normalizes
  rw [abelian_replacement_eq_intersection_normal_product target normal derived_le conjugator member normalizes]
  exact (le_inf ((le_inf le_rfl control.2).trans (Subgroup.inf_normalizer_le_normalizer_inf))
    (normalizer_inf_of_le _ _ _ product_control.2.1 Subgroup.le_normalizer_of_normal)).trans
      (Subgroup.inf_normalizer_le_normalizer_sup _ _)

variable [Finite GroupType]

theorem abelian_replacement_conjugator_normalizes (target normal : Subgroup GroupType) [normal.Normal]
    (derived_le : ⁅normal, normal⁆ ≤ target) (conjugator : GroupType) (member : conjugator ∈ normal) :
    conjugator ∈ Subgroup.normalizer (abelianReplacement target conjugator : Set GroupType) := by
  let intersection := abelianReplacementIntersection target conjugator
  let differences := abelianReplacementDifferences target conjugator
  let replacement := abelianReplacement target conjugator
  have derived_intersection := abelian_replacement_contains_derived target normal derived_le conjugator member
  have difference_normal := abelian_replacement_difference_le_normal target normal conjugator member
  have intersection_image : intersection.map (MulAut.conj conjugator).toMonoidHom ≤ replacement := by
    rintro _ ⟨element, element_member, rfl⟩
    have generator : conjugationDifference conjugator element ∈ differences :=
      Subgroup.subset_closure ⟨⟨element, element_member.1⟩, rfl⟩
    have product := replacement.mul_mem (Subgroup.mem_sup_left element_member) (Subgroup.mem_sup_right generator)
    change conjugator * element * conjugator⁻¹ ∈ replacement
    simpa only [conjugationDifference, ← mul_assoc, mul_inv_cancel, one_mul] using product
  have difference_image : differences.map (MulAut.conj conjugator).toMonoidHom ≤ replacement := by
    rintro _ ⟨element, element_member, rfl⟩
    have commutator_member : ⁅conjugator, element⁆ ∈ ⁅normal, normal⁆ :=
      Subgroup.commutator_mem_commutator member (difference_normal element_member)
    have product := replacement.mul_mem (Subgroup.mem_sup_left (derived_intersection commutator_member))
      (Subgroup.mem_sup_right element_member)
    change conjugator * element * conjugator⁻¹ ∈ replacement
    simpa only [commutatorElement_def, mul_assoc, inv_mul_cancel, mul_one] using product
  have image_le : replacement.map (MulAut.conj conjugator).toMonoidHom ≤ replacement := by
    change (intersection ⊔ differences).map (MulAut.conj conjugator).toMonoidHom ≤ replacement
    rw [Subgroup.map_sup]
    exact sup_le intersection_image difference_image
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  exact Subgroup.eq_of_le_of_card_ge image_le
    (by rw [Subgroup.card_map_of_injective (MulAut.conj conjugator).injective])

theorem abelian_replacement_strict_normalizer_growth (target normal : Subgroup GroupType) [normal.Normal]
    (derived_le : ⁅normal, normal⁆ ≤ target) (abelian : IsMulCommutative target)
    (conjugator : GroupType) (member : conjugator ∈ normal)
    (outside : conjugator ∉ Subgroup.normalizer (target : Set GroupType))
    (normalizes : conjugator ∈ Subgroup.normalizer
      (Subgroup.normalizer (target : Set GroupType) : Set GroupType)) :
    normal ⊓ Subgroup.normalizer (target : Set GroupType) <
      normal ⊓ Subgroup.normalizer (abelianReplacement target conjugator : Set GroupType) := by
  apply lt_of_le_of_ne
  · exact inf_le_inf_left _ (abelian_replacement_old_normalizer_normalizes target normal derived_le abelian
      conjugator member normalizes)
  · intro equality
    have new_member : conjugator ∈ normal ⊓ Subgroup.normalizer (abelianReplacement target conjugator : Set GroupType) :=
      ⟨member, abelian_replacement_conjugator_normalizes target normal derived_le conjugator member⟩
    rw [← equality] at new_member
    exact outside new_member.2

end CFSG.SignalizerFunctor.Helpers
