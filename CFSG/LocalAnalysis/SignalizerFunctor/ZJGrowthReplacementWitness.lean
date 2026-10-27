module

public import CFSG.LocalAnalysis.SignalizerFunctor.ZJGrowthClassTwo
public import CFSG.LocalAnalysis.SignalizerFunctor.ThompsonAmbientReplacement
public import CFSG.LocalAnalysis.SignalizerFunctor.ThompsonEmbeddedOvergroup

public section

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]

theorem zj_growth_replacement_witness (prime : ℕ) (prime_prime : prime.Prime) (odd_prime : prime ≠ 2)
    (stable : normalPSubgroupActionsStable prime GroupType)
    (self_centralizing : Subgroup.centralizer
      (primeSetCore (GroupType := GroupType) {prime} : Set GroupType) ≤ primeSetCore {prime})
    (sylow : Sylow prime GroupType) (kernel : Subgroup GroupType) [kernel.Normal]
    (proper : kernel < embeddedOrderThompsonCenter (sylow : Subgroup GroupType))
    (omits : ¬ zjGrowthClosure (sylow : Subgroup GroupType) kernel ≤
      embeddedOrderThompsonCenter (sylow : Subgroup GroupType)) :
    let base : Subgroup GroupType := sylow
    let closure := zjGrowthClosure base kernel
    let _normal := zj_growth_closure_normal base kernel
    let actionCore := conjugationActionPrimeCore prime closure
    let intersection := base ⊓ actionCore
    ∃ target : Subgroup base,
      target ∈ maximumOrderAbelianFamily base ∧
      ¬ closure ≤ target.map base.subtype ∧
      target.map base.subtype ≤ intersection ∧
      (target.map base.subtype).subgroupOf intersection ∈ maximumOrderAbelianFamily intersection ∧
      embeddedOrderThompsonCenter base ≤ embeddedOrderThompsonCenter intersection := by
  let base : Subgroup GroupType := sylow
  let closure := zjGrowthClosure base kernel
  let _normal := zj_growth_closure_normal base kernel
  let actionCore := conjugationActionPrimeCore prime closure
  let intersection := base ⊓ actionCore
  have properties := zj_growth_closure_class_two_properties prime prime_prime stable self_centralizing
    sylow kernel proper
  have core_le : primeSetCore (GroupType := GroupType) {prime} ≤ base := by
    let := prime_set_core_normal (GroupType := GroupType) {prime}
    exact (prime_core_isPGroup prime prime_prime).le_sylow_of_normal sylow
  have closure_le : closure ≤ base := properties.2.1.trans core_le
  have class_two : ⁅closure, closure⁆ ≤ Subgroup.centralizer (closure : Set GroupType) :=
    properties.2.2.2.1.trans properties.2.2.2.2
  obtain ⟨target, target_member, target_omits, normalized⟩ :=
    maximum_order_abelian_ambient_normalized_replacement prime prime_prime odd_prime base closure
      sylow.isPGroup' closure_le class_two (properties.2.2.2.1.trans proper.le) omits
  have target_le : target.map base.subtype ≤ intersection := by
    apply le_inf (Subgroup.map_subtype_le target)
    let := target_member.1
    have target_abelian : IsMulCommutative (target.map base.subtype) := inferInstance
    intro actorElement actor_member
    exact stable closure _normal ((prime_core_isPGroup prime prime_prime).to_le properties.2.1)
      actorElement (fun element => abelian_normalized_quadratic_conjugation _ closure target_abelian
        normalized ⟨actorElement, actor_member⟩ element)
  exact ⟨target, target_member, target_omits, target_le,
    embedded_maximum_order_abelian_family_subgroupOf base intersection inf_le_left target target_member target_le,
    embedded_order_thompson_center_overgroup base intersection inf_le_left target target_member target_le⟩

end CFSG.SignalizerFunctor.Helpers
