module

public import CFSG.LocalAnalysis.SignalizerFunctor.SubgroupProductCardinality
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

universe groupUniverse indexUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType]

def setLeftStabilizer (subset : Set GroupType) : Subgroup GroupType where
  carrier := {element | ∀ value : GroupType, element * value ∈ subset ↔ value ∈ subset}
  one_mem' := by intro value; rw [one_mul]
  mul_mem' := by
    intro first second first_member second_member value
    rw [mul_assoc, first_member, second_member]
  inv_mem' := by
    intro element member value
    have equivalence := member (element⁻¹ * value)
    rw [mul_inv_cancel_left] at equivalence
    exact equivalence.symm

theorem set_left_stabilizer_of_inclusions (subset : Set GroupType) (element : GroupType)
    (forward : ∀ value ∈ subset, element * value ∈ subset)
    (backward : ∀ value ∈ subset, element⁻¹ * value ∈ subset) :
    element ∈ setLeftStabilizer subset := by
  intro value
  constructor
  · intro member
    have original := backward (element * value) member
    rwa [inv_mul_cancel_left] at original
  · exact forward value

theorem subgroup_product_left_stabilized (first second localFactor localCore control : Subgroup GroupType)
    (localFactor_le : localFactor ≤ second) (localCore_le : localCore ≤ first)
    (control_le : control ≤ first)
    (local_normalizes : localFactor ≤ Subgroup.normalizer (localCore : Set GroupType))
    (control_normalizes : control ≤ Subgroup.normalizer (second : Set GroupType))
    (splitting : subgroupProduct localCore control = (first : Set GroupType)) :
    localFactor ≤ setLeftStabilizer (subgroupProduct first second) := by
  have forward : ∀ localElement ∈ localFactor, ∀ value ∈ subgroupProduct first second,
      localElement * value ∈ subgroupProduct first second := by
    rintro localElement local_member value ⟨firstElement, first_member, secondElement, second_member, rfl⟩
    have split_member : firstElement ∈ subgroupProduct localCore control := by rw [splitting]; exact first_member
    obtain ⟨coreElement, core_member, controlElement, control_member, product_eq⟩ := split_member
    let conjugated := localElement * coreElement * localElement⁻¹
    have conjugated_member : conjugated ∈ localCore :=
      Subgroup.le_normalizer_iff.mp local_normalizes localElement local_member coreElement core_member
    let secondConjugated := controlElement⁻¹ * localElement * controlElement
    have second_conjugated_member : secondConjugated ∈ second := by
      simpa only [inv_inv] using Subgroup.le_normalizer_iff.mp control_normalizes controlElement⁻¹
        (control.inv_mem control_member) localElement (localFactor_le local_member)
    refine ⟨conjugated * controlElement,
      first.mul_mem (localCore_le conjugated_member) (control_le control_member),
      secondConjugated * secondElement, second.mul_mem second_conjugated_member second_member, ?_⟩
    rw [← product_eq]
    dsimp only [conjugated, secondConjugated]
    group
  intro localElement member
  exact set_left_stabilizer_of_inclusions _ localElement
    (forward localElement member) (forward localElement⁻¹ (localFactor.inv_mem member))

theorem permuting_subgroup_product_eq_sup (first second : Subgroup GroupType)
    (preserved : second ≤ setLeftStabilizer (subgroupProduct first second)) :
    subgroupProduct first second = ((first ⊔ second : Subgroup GroupType) : Set GroupType) ∧
      subgroupProduct second first = subgroupProduct first second := by
  have second_first_le : subgroupProduct second first ⊆ subgroupProduct first second := by
    rintro value ⟨secondElement, second_member, firstElement, first_member, rfl⟩
    have first_product : firstElement ∈ subgroupProduct first second :=
      ⟨firstElement, first_member, 1, second.one_mem, mul_one _⟩
    exact (preserved second_member firstElement).mpr first_product
  let productSubgroup : Subgroup GroupType :=
    { carrier := subgroupProduct first second
      one_mem' := ⟨1, first.one_mem, 1, second.one_mem, one_mul _⟩
      mul_mem' := by
        rintro firstValue secondValue ⟨firstElement, first_member, secondElement, second_member, rfl⟩
          ⟨otherFirst, other_first_member, otherSecond, other_second_member, rfl⟩
        have middle : secondElement * otherFirst ∈ subgroupProduct first second :=
          second_first_le ⟨secondElement, second_member, otherFirst, other_first_member, rfl⟩
        obtain ⟨middleFirst, middle_first_member, middleSecond, middle_second_member, middle_product⟩ := middle
        refine ⟨firstElement * middleFirst, first.mul_mem first_member middle_first_member,
          middleSecond * otherSecond, second.mul_mem middle_second_member other_second_member, ?_⟩
        change (firstElement * middleFirst) * (middleSecond * otherSecond) =
          (firstElement * secondElement) * (otherFirst * otherSecond)
        change middleFirst * middleSecond = secondElement * otherFirst at middle_product
        calc
          (firstElement * middleFirst) * (middleSecond * otherSecond) =
            firstElement * (middleFirst * middleSecond) * otherSecond := by group
          _ = firstElement * (secondElement * otherFirst) * otherSecond := by rw [middle_product]
          _ = (firstElement * secondElement) * (otherFirst * otherSecond) := by group
      inv_mem' := by
        rintro value ⟨firstElement, first_member, secondElement, second_member, rfl⟩
        rw [mul_inv_rev]
        exact second_first_le ⟨secondElement⁻¹, second.inv_mem second_member,
          firstElement⁻¹, first.inv_mem first_member, rfl⟩ }
  have subgroup_eq : productSubgroup = first ⊔ second := by
    apply le_antisymm
    · rintro value ⟨firstElement, first_member, secondElement, second_member, rfl⟩
      exact (first ⊔ second).mul_mem (Subgroup.mem_sup_left first_member) (Subgroup.mem_sup_right second_member)
    · apply sup_le
      · intro element member
        exact ⟨element, member, 1, second.one_mem, mul_one _⟩
      · intro element member
        exact ⟨1, first.one_mem, element, member, one_mul _⟩
  refine ⟨congrArg (fun subgroup : Subgroup GroupType => (subgroup : Set GroupType)) subgroup_eq, ?_⟩
  apply Set.Subset.antisymm second_first_le
  rintro value ⟨firstElement, first_member, secondElement, second_member, rfl⟩
  have inverse_member : secondElement⁻¹ * firstElement⁻¹ ∈ subgroupProduct first second :=
    second_first_le ⟨secondElement⁻¹, second.inv_mem second_member, firstElement⁻¹, first.inv_mem first_member, rfl⟩
  obtain ⟨inverseFirst, inverse_first_member, inverseSecond, inverse_second_member, inverse_product⟩ := inverse_member
  refine ⟨inverseSecond⁻¹, second.inv_mem inverse_second_member,
    inverseFirst⁻¹, first.inv_mem inverse_first_member, ?_⟩
  have product_eq := congrArg Inv.inv inverse_product
  simpa only [mul_inv_rev, inv_inv] using product_eq

theorem generated_local_factors_product_eq_sup {Index : Sort indexUniverse}
    (first second control : Subgroup GroupType) (localFactors localCores : Index → Subgroup GroupType)
    (generation : (⨆ index, localFactors index) = second)
    (localFactors_le : ∀ index, localFactors index ≤ second)
    (localCores_le : ∀ index, localCores index ≤ first)
    (control_le : control ≤ first)
    (local_normalizes : ∀ index, localFactors index ≤ Subgroup.normalizer (localCores index : Set GroupType))
    (control_normalizes : control ≤ Subgroup.normalizer (second : Set GroupType))
    (splitting : ∀ index, subgroupProduct (localCores index) control = (first : Set GroupType)) :
    subgroupProduct first second = ((first ⊔ second : Subgroup GroupType) : Set GroupType) ∧
      subgroupProduct second first = subgroupProduct first second := by
  apply permuting_subgroup_product_eq_sup
  conv_lhs => rw [← generation]
  apply iSup_le
  intro index
  exact subgroup_product_left_stabilized first second (localFactors index) (localCores index) control
    (localFactors_le index) (localCores_le index) control_le (local_normalizes index) control_normalizes
    (splitting index)

end CFSG.SignalizerFunctor.Helpers
