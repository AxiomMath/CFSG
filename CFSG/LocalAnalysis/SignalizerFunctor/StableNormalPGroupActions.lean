module

public import CFSG.LocalAnalysis.SignalizerFunctor.MatsuyamaWeakClosure
public import CFSG.LocalAnalysis.SignalizerFunctor.ActionPrimeCore
public import CFSG.LocalAnalysis.SignalizerFunctor.ZJGrowthFixedSubgroup

public section

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType]

@[expose] def normalPSubgroupActionsStable (prime : ℕ) (GroupType : Type groupUniverse) [Group GroupType] : Prop :=
  ∀ (base : Subgroup GroupType) (_normal : base.Normal), IsPGroup prime base →
    ∀ actorElement : GroupType,
      (∀ element : base,
        conjugationDifference actorElement (conjugationDifference actorElement element.val) = 1) →
      actorElement ∈ conjugationActionPrimeCore prime base

theorem abelian_normalized_quadratic_conjugation (target acting : Subgroup GroupType)
    (abelian : IsMulCommutative target)
    (normalized : acting ≤ Subgroup.normalizer (target : Set GroupType))
    (actorElement : target) (element : acting) :
    conjugationDifference actorElement.val (conjugationDifference actorElement.val element.val) = 1 := by
  let := abelian
  have first_member : conjugationDifference actorElement.val element.val ∈ target := by
    have conjugated := Subgroup.le_normalizer_iff.mp normalized element.val⁻¹
      (acting.inv_mem element.property) actorElement.val actorElement.property
    have contained := target.mul_mem conjugated (target.inv_mem actorElement.property)
    simpa only [conjugationDifference, inv_inv] using contained
  have commute_eq := congrArg Subtype.val (mul_comm' actorElement
    (⟨conjugationDifference actorElement.val element.val, first_member⟩ : target))
  change actorElement.val * conjugationDifference actorElement.val element.val =
    conjugationDifference actorElement.val element.val * actorElement.val at commute_eq
  change (conjugationDifference actorElement.val element.val)⁻¹ * actorElement.val *
    conjugationDifference actorElement.val element.val * actorElement.val⁻¹ = 1
  rw [mul_assoc (conjugationDifference actorElement.val element.val)⁻¹ actorElement.val
    (conjugationDifference actorElement.val element.val), commute_eq]
  group

variable [Finite GroupType]

theorem stable_abelian_subgroup_le_prime_core (prime : ℕ) (prime_prime : prime.Prime)
    (stable : normalPSubgroupActionsStable prime GroupType)
    (self_centralizing : Subgroup.centralizer
      (primeSetCore (GroupType := GroupType) {prime} : Set GroupType) ≤ primeSetCore {prime})
    (sylow : Sylow prime GroupType) (target : Subgroup GroupType)
    (abelian : IsMulCommutative target)
    (normalized : (sylow : Subgroup GroupType) ≤ Subgroup.normalizer (target : Set GroupType)) :
    target ≤ primeSetCore {prime} := by
  let core := primeSetCore (GroupType := GroupType) {prime}
  let _normal := prime_set_core_normal (GroupType := GroupType) {prime}
  have pgroup := prime_core_isPGroup (GroupType := GroupType) prime prime_prime
  have core_le : core ≤ (sylow : Subgroup GroupType) := pgroup.le_sylow_of_normal sylow
  have kernel_pgroup := pgroup.to_le self_centralizing
  intro actorElement member
  have stable_member := stable core _normal pgroup actorElement (fun element =>
    abelian_normalized_quadratic_conjugation target core abelian (core_le.trans normalized)
      ⟨actorElement, member⟩ element)
  rwa [conjugation_action_prime_core_eq_prime_core prime prime_prime core kernel_pgroup] at stable_member

@[expose] def zjGrowthClosure (sylowBase kernel : Subgroup GroupType) [kernel.Normal] : Subgroup GroupType :=
  normalizedConjugateHull ⊤ (zjGrowthFixedSubgroup sylowBase kernel)

omit [Finite GroupType] in
theorem zj_growth_closure_normal (sylowBase kernel : Subgroup GroupType) [kernel.Normal] :
    (zjGrowthClosure sylowBase kernel).Normal := by
  apply Subgroup.normalizer_eq_top_iff.mp
  exact top_le_iff.mp (normalized_conjugate_hull_normalized ⊤ (zjGrowthFixedSubgroup sylowBase kernel))

theorem zj_growth_closure_le_prime_core (prime : ℕ) (prime_prime : prime.Prime)
    (stable : normalPSubgroupActionsStable prime GroupType)
    (self_centralizing : Subgroup.centralizer
      (primeSetCore (GroupType := GroupType) {prime} : Set GroupType) ≤ primeSetCore {prime})
    (sylow : Sylow prime GroupType) (kernel : Subgroup GroupType) [kernel.Normal]
    (proper : kernel < embeddedOrderThompsonCenter (sylow : Subgroup GroupType)) :
    zjGrowthFixedSubgroup (sylow : Subgroup GroupType) kernel ≤ primeSetCore {prime} ∧
      zjGrowthClosure (sylow : Subgroup GroupType) kernel ≤ primeSetCore {prime} := by
  have properties := zj_growth_fixed_subgroup_properties prime prime_prime _ kernel sylow.isPGroup' proper
  have fixed_le := stable_abelian_subgroup_le_prime_core prime prime_prime stable self_centralizing sylow
    _ properties.2.2.1 properties.2.2.2.1
  let := prime_set_core_normal (GroupType := GroupType) {prime}
  exact ⟨fixed_le, normalized_conjugate_hull_le ⊤ _ _ fixed_le Subgroup.le_normalizer_of_normal⟩

end CFSG.SignalizerFunctor.Helpers
