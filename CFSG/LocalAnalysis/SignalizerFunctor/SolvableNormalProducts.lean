module

public import CFSG.Mathlib.GroupTheory.Basic
public import CFSG.LocalAnalysis.SignalizerFunctor.NormalProduct
public import CFSG.LocalAnalysis.SignalizerFunctor.HallTransport

public section

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType]

def normalProductQuotientHom (normal other : Subgroup GroupType)
    (normalizes : other ≤ Subgroup.normalizer (normal : Set GroupType)) :
    let combined := normal ⊔ other
    let _normal : (normal.subgroupOf combined).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
        (sup_le Subgroup.le_normalizer normalizes)
    other →* combined ⧸ normal.subgroupOf combined := by
  let combined := normal ⊔ other
  let _normal : (normal.subgroupOf combined).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le Subgroup.le_normalizer normalizes)
  exact (QuotientGroup.mk' (normal.subgroupOf combined)).comp
    (Subgroup.inclusion (le_sup_right : other ≤ combined))

theorem normal_product_quotient_hom_surjective (normal other : Subgroup GroupType)
    (normalizes : other ≤ Subgroup.normalizer (normal : Set GroupType)) :
    let combined := normal ⊔ other
    let _normal : (normal.subgroupOf combined).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
        (sup_le Subgroup.le_normalizer normalizes)
    Function.Surjective (normalProductQuotientHom normal other normalizes) := by
  let combined := normal ⊔ other
  let _normal : (normal.subgroupOf combined).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le Subgroup.le_normalizer normalizes)
  change Function.Surjective (normalProductQuotientHom normal other normalizes)
  intro quotientElement
  obtain ⟨element, rfl⟩ := QuotientGroup.mk'_surjective (normal.subgroupOf combined) quotientElement
  obtain ⟨normalElement, normal_member, otherElement, other_member, equality⟩ :=
    (mem_sup_of_normalizing normal other normalizes element.val).mp element.property
  refine ⟨⟨otherElement, other_member⟩, ?_⟩
  let projection := QuotientGroup.mk' (normal.subgroupOf combined)
  have internal_equal : (⟨normalElement, Subgroup.mem_sup_left normal_member⟩ : combined) *
      ⟨otherElement, Subgroup.mem_sup_right other_member⟩ = element := Subtype.ext equality
  have normal_trivial : projection (⟨normalElement, Subgroup.mem_sup_left normal_member⟩ : combined) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr normal_member
  change projection (⟨otherElement, Subgroup.mem_sup_right other_member⟩ : combined) = projection element
  rw [← internal_equal, map_mul, normal_trivial, one_mul]

theorem prime_supported_sup_of_normalizing (primes : Set ℕ) (normal other : Subgroup GroupType)
    (normalizes : other ≤ Subgroup.normalizer (normal : Set GroupType))
    (normal_supported : primeSupported primes (Nat.card normal))
    (other_supported : primeSupported primes (Nat.card other)) :
    primeSupported primes (Nat.card (normal ⊔ other : Subgroup GroupType)) := by
  let combined := normal ⊔ other
  let _normal : (normal.subgroupOf combined).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le Subgroup.le_normalizer normalizes)
  have quotient_supported : primeSupported primes (Nat.card (combined ⧸ normal.subgroupOf combined)) :=
    prime_supported_of_dvd primes other_supported (CFSG.card_dvd_of_surjective
      (normalProductQuotientHom normal other normalizes)
      (normal_product_quotient_hom_surjective normal other normalizes))
  have internal_supported : primeSupported primes (Nat.card (normal.subgroupOf combined)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left : normal ≤ combined)).toEquiv]
    exact normal_supported
  have card_formula := (normal.subgroupOf combined).card_mul_index
  rw [Subgroup.index_eq_card] at card_formula
  rw [← card_formula]
  exact prime_supported_mul primes internal_supported quotient_supported

theorem solvable_sup_of_normalizing (normal other : Subgroup GroupType)
    (normalizes : other ≤ Subgroup.normalizer (normal : Set GroupType))
    (normal_solvable : Group.IsSolvable normal) (other_solvable : Group.IsSolvable other) :
    Group.IsSolvable (normal ⊔ other : Subgroup GroupType) := by
  let := normal_solvable
  let := other_solvable
  let combined := normal ⊔ other
  let _normal : (normal.subgroupOf combined).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le Subgroup.le_normalizer normalizes)
  let _quotientSolvable : Group.IsSolvable (combined ⧸ normal.subgroupOf combined) :=
    Group.isSolvable_of_surjective (normal_product_quotient_hom_surjective normal other normalizes)
  let inclusion := Subgroup.inclusion (le_sup_left : normal ≤ combined)
  let projection := QuotientGroup.mk' (normal.subgroupOf combined)
  apply Group.isSolvable_of_ker_le_range inclusion projection
  rw [QuotientGroup.ker_mk']
  intro element member
  exact ⟨⟨element.val, member⟩, rfl⟩

end CFSG.SignalizerFunctor.Helpers
