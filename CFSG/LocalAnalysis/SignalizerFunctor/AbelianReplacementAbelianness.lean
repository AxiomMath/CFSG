module

public import CFSG.LocalAnalysis.SignalizerFunctor.ThompsonCenterIntersection
public import CFSG.LocalAnalysis.SignalizerFunctor.AbelianReplacementControl

public section

open scoped commutatorElement

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType]

theorem abelian_replacement_differences_abelian
    (prime : ℕ) (prime_prime : prime.Prime) (odd_prime : prime ≠ 2)
    (target normal : Subgroup GroupType) [normal.Normal] (pgroup : IsPGroup prime normal)
    (abelian : IsMulCommutative target)
    (class_two : ⁅normal, normal⁆ ≤ Subgroup.centralizer (normal : Set GroupType))
    (derived_le : ⁅normal, normal⁆ ≤ target) (conjugator : GroupType) (member : conjugator ∈ normal)
    (normalizes : conjugator ∈ Subgroup.normalizer
      (Subgroup.normalizer (target : Set GroupType) : Set GroupType)) :
    IsMulCommutative (abelianReplacementDifferences target conjugator) := by
  let := abelian
  let parent := target ⊔ conjugateSubgroup conjugator target
  have control := normalizer_conjugate_abelian_product_control target abelian conjugator normalizes
  have fixed_derived : target ≤ Subgroup.centralizer ((⁅normal, normal⁆ : Subgroup GroupType) : Set GroupType) :=
    (Subgroup.le_centralizer target).trans (Subgroup.centralizer_le derived_le)
  have differences_le : ∀ actorElement : target,
      conjugationDifference actorElement.val conjugator⁻¹ ∈ parent := by
    intro actorElement
    unfold conjugationDifference
    rw [inv_inv]
    exact parent.mul_mem (Subgroup.mem_sup_right
      (Subgroup.mem_map_of_mem (MulAut.conj conjugator).toMonoidHom actorElement.property))
      (Subgroup.mem_sup_left (target.inv_mem actorElement.property))
  have cubic : ∀ first second third : target,
      conjugationDifference third.val
        (conjugationDifference second.val (conjugationDifference first.val conjugator⁻¹)) = 1 := by
    intro first second third
    have first_member := differences_le first
    have difference_derived : conjugationDifference second.val
        (conjugationDifference first.val conjugator⁻¹) ∈ ⁅parent, parent⁆ := by
      have generated := Subgroup.commutator_mem_commutator (H₁ := parent) (H₂ := parent)
        (parent.inv_mem first_member) (Subgroup.mem_sup_left second.property)
      change ⁅(conjugationDifference first.val conjugator⁻¹)⁻¹, second.val⁆ ∈ ⁅parent, parent⁆ at generated
      simpa only [conjugationDifference, commutatorElement_def, inv_inv] using generated
    have central := control.2.2.2 (control.2.2.1 difference_derived)
    have commutes := Subgroup.mem_centralizer_iff.mp central third.val (Subgroup.mem_sup_left third.property)
    let difference := conjugationDifference second.val (conjugationDifference first.val conjugator⁻¹)
    change difference⁻¹ * third.val * difference * third.val⁻¹ = 1
    calc
      _ = difference⁻¹ * (third.val * difference) * third.val⁻¹ := by group
      _ = difference⁻¹ * (difference * third.val) * third.val⁻¹ := by rw [commutes]
      _ = 1 := by group
  have ambient_abelian := ambient_class_two_cubic_differences_abelian prime prime_prime odd_prime target normal
    pgroup abelian (Subgroup.le_normalizer_of_normal) class_two fixed_derived conjugator⁻¹ (normal.inv_mem member) cubic
  let := ambient_abelian
  apply CFSG.subgroup_isMulCommutative_closure
  rintro _ ⟨first, rfl⟩ _ ⟨second, rfl⟩
  let differences := Subgroup.closure (Set.range (fun actorElement : target =>
    conjugationDifference actorElement.val conjugator⁻¹))
  have first_member : conjugationDifference first.val⁻¹ conjugator⁻¹ ∈ differences :=
    Subgroup.subset_closure ⟨first⁻¹, rfl⟩
  have second_member : conjugationDifference second.val⁻¹ conjugator⁻¹ ∈ differences :=
    Subgroup.subset_closure ⟨second⁻¹, rfl⟩
  have commutes : Commute (conjugationDifference first.val⁻¹ conjugator⁻¹)
      (conjugationDifference second.val⁻¹ conjugator⁻¹) :=
    congrArg Subtype.val (mul_comm' (⟨_, first_member⟩ : differences) (⟨_, second_member⟩ : differences))
  have first_formula : (conjugationDifference first.val⁻¹ conjugator⁻¹)⁻¹ =
      conjugationDifference conjugator first.val := by unfold conjugationDifference; group
  have second_formula : (conjugationDifference second.val⁻¹ conjugator⁻¹)⁻¹ =
      conjugationDifference conjugator second.val := by unfold conjugationDifference; group
  change conjugationDifference conjugator first.val * conjugationDifference conjugator second.val =
    conjugationDifference conjugator second.val * conjugationDifference conjugator first.val
  rw [← first_formula, ← second_formula]
  exact commutes.inv_inv.eq

theorem abelian_replacement_abelian
    (prime : ℕ) (prime_prime : prime.Prime) (odd_prime : prime ≠ 2)
    (target normal : Subgroup GroupType) [normal.Normal] (pgroup : IsPGroup prime normal)
    (abelian : IsMulCommutative target)
    (class_two : ⁅normal, normal⁆ ≤ Subgroup.centralizer (normal : Set GroupType))
    (derived_le : ⁅normal, normal⁆ ≤ target) (conjugator : GroupType) (member : conjugator ∈ normal)
    (normalizes : conjugator ∈ Subgroup.normalizer
      (Subgroup.normalizer (target : Set GroupType) : Set GroupType)) :
    IsMulCommutative (abelianReplacement target conjugator) := by
  let := abelian
  have control := normalizer_conjugate_abelian_product_control target abelian conjugator normalizes
  have differences_abelian := abelian_replacement_differences_abelian prime prime_prime odd_prime target normal
    pgroup abelian class_two derived_le conjugator member normalizes
  have intersection_abelian : IsMulCommutative (abelianReplacementIntersection target conjugator) := by
    apply Subgroup.le_centralizer_iff_isMulCommutative.mp
    exact (inf_le_left.trans (Subgroup.le_centralizer target)).trans
      (Subgroup.centralizer_le inf_le_left)
  exact commuting_abelian_sup (abelianReplacementIntersection target conjugator)
    (abelianReplacementDifferences target conjugator) intersection_abelian differences_abelian
    ((abelian_replacement_difference_le_product target conjugator).trans
      (Subgroup.le_centralizer_iff.mp control.2.2.2))

end CFSG.SignalizerFunctor.Helpers
