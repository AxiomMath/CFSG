module

public import CFSG.LocalAnalysis.SignalizerFunctor.ThompsonSubgroupTransport
public import CFSG.LocalAnalysis.SignalizerFunctor.PGroupFixedQuotientEscape

public section

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]

@[expose] def zjGrowthFixedSubgroup (sylowBase kernel : Subgroup GroupType) [kernel.Normal] :
    Subgroup GroupType :=
  embeddedOrderThompsonCenter sylowBase ⊓
    (Subgroup.centralizer (sylowBase.map (QuotientGroup.mk' kernel) : Set (GroupType ⧸ kernel))).comap
      (QuotientGroup.mk' kernel)

omit [Finite GroupType] in
theorem zj_growth_fixed_difference_iff (sylowBase kernel : Subgroup GroupType) [kernel.Normal]
    (element : GroupType) :
    element ∈ (Subgroup.centralizer
      (sylowBase.map (QuotientGroup.mk' kernel) : Set (GroupType ⧸ kernel))).comap
        (QuotientGroup.mk' kernel) ↔
      ∀ actorElement : sylowBase, conjugationDifference actorElement.val element ∈ kernel := by
  let projection := QuotientGroup.mk' kernel
  constructor
  · intro member actorElement
    have commute_eq := Subgroup.mem_centralizer_iff.mp member (projection actorElement.val)
      (Subgroup.mem_map_of_mem projection actorElement.property)
    change projection actorElement.val * projection element =
      projection element * projection actorElement.val at commute_eq
    have difference_one : projection (conjugationDifference actorElement.val element) = 1 := by
      simp only [conjugationDifference, map_mul, map_inv]
      rw [mul_assoc (projection element)⁻¹ (projection actorElement.val) (projection element), commute_eq]
      group
    exact (QuotientGroup.eq_one_iff _).mp difference_one
  · intro differences
    apply Subgroup.mem_centralizer_iff.mpr
    rintro _ ⟨actorElement, actor_member, rfl⟩
    have identity := (QuotientGroup.eq_one_iff _).mpr (differences ⟨actorElement, actor_member⟩)
    change projection (conjugationDifference actorElement element) = 1 at identity
    simp only [conjugationDifference, map_mul, map_inv] at identity
    calc
      projection actorElement * projection element =
          projection element *
            ((projection element)⁻¹ * projection actorElement * projection element *
              (projection actorElement)⁻¹) * projection actorElement := by group
      _ = projection element * projection actorElement := by rw [identity]; group

theorem zj_growth_fixed_subgroup_properties (prime : ℕ) (prime_prime : prime.Prime)
    (sylowBase kernel : Subgroup GroupType) [kernel.Normal]
    (base_pgroup : IsPGroup prime sylowBase)
    (proper : kernel < embeddedOrderThompsonCenter sylowBase) :
    kernel < zjGrowthFixedSubgroup sylowBase kernel ∧
      zjGrowthFixedSubgroup sylowBase kernel ≤ embeddedOrderThompsonCenter sylowBase ∧
      IsMulCommutative (zjGrowthFixedSubgroup sylowBase kernel) ∧
      sylowBase ≤ Subgroup.normalizer (zjGrowthFixedSubgroup sylowBase kernel : Set GroupType) ∧
      ∀ element : zjGrowthFixedSubgroup sylowBase kernel, ∀ actorElement : sylowBase,
        conjugationDifference actorElement.val element.val ∈ kernel := by
  let center := embeddedOrderThompsonCenter sylowBase
  have center_properties := embedded_order_thompson_center_properties sylowBase sylowBase
    Subgroup.le_normalizer
  have fixed_contains : kernel ≤ zjGrowthFixedSubgroup sylowBase kernel := by
    intro element member
    refine ⟨proper.le member, ?_⟩
    change QuotientGroup.mk' kernel element ∈ Subgroup.centralizer
      (sylowBase.map (QuotientGroup.mk' kernel) : Set (GroupType ⧸ kernel))
    have image_one : QuotientGroup.mk' kernel element = 1 := (QuotientGroup.eq_one_iff _).mpr member
    rw [image_one]
    exact Subgroup.one_mem _
  have quotient_normal : (kernel.subgroupOf center).Normal := inferInstance
  obtain ⟨element, center_member, outside, differences⟩ := pgroup_fixed_quotient_escape prime prime_prime
    sylowBase center kernel base_pgroup (base_pgroup.to_le center_properties.1)
    center_properties.2.2 quotient_normal Subgroup.le_normalizer_of_normal proper
  have fixed_member : element ∈ zjGrowthFixedSubgroup sylowBase kernel :=
    ⟨center_member, (zj_growth_fixed_difference_iff sylowBase kernel element).mpr differences⟩
  have normalized : sylowBase ≤ Subgroup.normalizer
      (zjGrowthFixedSubgroup sylowBase kernel : Set GroupType) := by
    apply Subgroup.le_normalizer_iff.mpr
    intro actorElement actor_member fixedElement fixed_member
    refine ⟨Subgroup.le_normalizer_iff.mp center_properties.2.2 actorElement actor_member fixedElement
      fixed_member.1, ?_⟩
    let projection := QuotientGroup.mk' kernel
    have commute_eq := Subgroup.mem_centralizer_iff.mp fixed_member.2 (projection actorElement)
      (Subgroup.mem_map_of_mem projection actor_member)
    change projection actorElement * projection fixedElement =
      projection fixedElement * projection actorElement at commute_eq
    have image_eq : projection (actorElement * fixedElement * actorElement⁻¹) = projection fixedElement := by
      rw [map_mul, map_mul, map_inv, commute_eq]
      group
    change projection (actorElement * fixedElement * actorElement⁻¹) ∈ Subgroup.centralizer
      (sylowBase.map projection : Set (GroupType ⧸ kernel))
    rw [image_eq]
    exact fixed_member.2
  let := center_properties.2.1
  have fixed_abelian : IsMulCommutative (zjGrowthFixedSubgroup sylowBase kernel) := by
    refine ⟨⟨?_⟩⟩
    intro first second
    apply Subtype.ext
    change first.val * second.val = second.val * first.val
    exact congrArg Subtype.val (mul_comm' (⟨first.val, first.property.1⟩ : center)
      (⟨second.val, second.property.1⟩ : center))
  refine ⟨lt_of_le_of_ne fixed_contains (fun equality => outside (equality.symm ▸ fixed_member)),
    inf_le_left, fixed_abelian, normalized, ?_⟩
  intro fixedElement actorElement
  exact (zj_growth_fixed_difference_iff sylowBase kernel fixedElement.val).mp fixedElement.property.2
    actorElement

end CFSG.SignalizerFunctor.Helpers
