module

public import CFSG.LocalAnalysis.SignalizerFunctor.NormalQuotientFrattini
public import CFSG.LocalAnalysis.SignalizerFunctor.ZJGrowthReplacementWitness

public section

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]

omit [Finite GroupType] in
theorem centralizer_normalizer_product_hull_le (normal target bound control : Subgroup GroupType)
    [normal.Normal] (target_le : target ≤ normal) (bound_le : target ≤ bound)
    (normalized : control ≤ Subgroup.normalizer (bound : Set GroupType))
    (product : Subgroup.centralizer (normal : Set GroupType) ⊔ control = ⊤) :
    normalizedConjugateHull ⊤ target ≤ bound := by
  apply iSup_le
  intro conjugator
  have product_member : conjugator.val ∈ Subgroup.centralizer (normal : Set GroupType) ⊔ control := by
    rw [product]
    exact Subgroup.mem_top _
  obtain ⟨centralizerElement, centralizer_member, normalizerElement, normalizer_member, equal⟩ :=
    Subgroup.mem_sup_of_normal_left.mp product_member
  rintro element ⟨original, original_member, image⟩
  have conjugate_member : normalizerElement * original * normalizerElement⁻¹ ∈ normal :=
    Subgroup.Normal.conj_mem inferInstance original (target_le original_member) normalizerElement
  have conjugate_bound : normalizerElement * original * normalizerElement⁻¹ ∈ bound :=
    Subgroup.le_normalizer_iff.mp normalized normalizerElement normalizer_member original
      (bound_le original_member)
  have commute_eq := Subgroup.mem_centralizer_iff.mp centralizer_member
    (normalizerElement * original * normalizerElement⁻¹) conjugate_member
  have conjugate_eq : conjugator.val * original * conjugator.val⁻¹ =
      normalizerElement * original * normalizerElement⁻¹ := by
    rw [← equal]
    calc
      (centralizerElement * normalizerElement) * original * (centralizerElement * normalizerElement)⁻¹ =
          centralizerElement * (normalizerElement * original * normalizerElement⁻¹) * centralizerElement⁻¹ := by group
      _ = (normalizerElement * original * normalizerElement⁻¹) * centralizerElement * centralizerElement⁻¹ := by
        rw [← commute_eq]
      _ = normalizerElement * original * normalizerElement⁻¹ := by group
  change conjugator.val * original * conjugator.val⁻¹ = element at image
  rw [conjugate_eq] at image
  exact image ▸ conjugate_bound

theorem zj_growth_closure_le_thompson_center (prime : ℕ) (prime_prime : prime.Prime)
    (odd_prime : prime ≠ 2) (stable : normalPSubgroupActionsStable prime GroupType)
    (self_centralizing : Subgroup.centralizer
      (primeSetCore (GroupType := GroupType) {prime} : Set GroupType) ≤ primeSetCore {prime})
    (sylow : Sylow prime GroupType) (kernel : Subgroup GroupType) [kernel.Normal]
    (proper : kernel < embeddedOrderThompsonCenter (sylow : Subgroup GroupType)) :
    zjGrowthClosure (sylow : Subgroup GroupType) kernel ≤
      embeddedOrderThompsonCenter (sylow : Subgroup GroupType) := by
  let base : Subgroup GroupType := sylow
  let fixed := zjGrowthFixedSubgroup base kernel
  let closure := zjGrowthClosure base kernel
  let _normal := zj_growth_closure_normal base kernel
  let actionCore := conjugationActionPrimeCore prime closure
  let intersection := base ⊓ actionCore
  by_contra omits
  obtain ⟨target, target_member, target_omits, target_le, target_internal_member, center_le⟩ :=
    zj_growth_replacement_witness prime prime_prime odd_prime stable self_centralizing sylow kernel proper omits
  let _actionCoreNormal := conjugation_action_prime_core_normal prime closure
  obtain ⟨internalSylow, embedded_eq⟩ := normal_subgroup_sylow_intersection prime prime_prime actionCore sylow
  have embedded_intersection : (internalSylow : Subgroup actionCore).map actionCore.subtype = intersection := by
    simpa only [intersection, inf_comm] using embedded_eq
  have frattini := (quotient_action_prime_core_frattini prime prime_prime
    (Subgroup.centralizer (closure : Set GroupType)) internalSylow).2
  change Subgroup.centralizer (closure : Set GroupType) ⊔ Subgroup.normalizer
    ((internalSylow : Subgroup actionCore).map actionCore.subtype : Set GroupType) = ⊤ at frattini
  rw [embedded_intersection] at frattini
  have fixed_le : fixed ≤ closure := subgroup_le_normalized_conjugate_hull ⊤ fixed
  have properties := zj_growth_fixed_subgroup_properties prime prime_prime base kernel sylow.isPGroup' proper
  have fixed_center_le : fixed ≤ embeddedOrderThompsonCenter intersection := properties.2.1.trans center_le
  have normalized := (embedded_order_thompson_center_properties intersection
    (Subgroup.normalizer (intersection : Set GroupType)) le_rfl).2.2
  have closure_center_le := centralizer_normalizer_product_hull_le closure fixed
    (embeddedOrderThompsonCenter intersection) (Subgroup.normalizer (intersection : Set GroupType))
    fixed_le fixed_center_le normalized frattini
  have center_target_le : embeddedOrderThompsonCenter intersection ≤ target.map base.subtype := by
    have internal_le : orderThompsonCenter intersection ≤
        (target.map base.subtype).subgroupOf intersection := by
      rw [order_thompson_center_eq_intersection]
      exact iInf_le_of_le _ (iInf_le_of_le target_internal_member le_rfl)
    have mapped_le := Subgroup.map_mono (f := intersection.subtype) internal_le
    rwa [Subgroup.map_subgroupOf_eq_of_le target_le] at mapped_le
  exact target_omits (closure_center_le.trans center_target_le)

end CFSG.SignalizerFunctor.Helpers
