module

public import CFSG.LocalAnalysis.SignalizerFunctor.ZJGrowthConjugateTrapping

public section

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]

theorem axiomatic_zj_normality (prime : ℕ) (prime_prime : prime.Prime) (odd_prime : prime ≠ 2)
    (stable : normalPSubgroupActionsStable prime GroupType)
    (self_centralizing : Subgroup.centralizer
      (primeSetCore (GroupType := GroupType) {prime} : Set GroupType) ≤ primeSetCore {prime})
    (sylow : Sylow prime GroupType) :
    (embeddedOrderThompsonCenter (sylow : Subgroup GroupType)).Normal := by
  classical
  let center := embeddedOrderThompsonCenter (sylow : Subgroup GroupType)
  let candidates := {kernel : Subgroup GroupType // kernel.Normal ∧ kernel ≤ center}
  let _nonempty : Nonempty candidates := ⟨⟨⊥, inferInstance, bot_le⟩⟩
  obtain ⟨candidate, optimal⟩ := Finite.exists_max (fun kernel : candidates => Nat.card kernel.val)
  by_cases equality : candidate.val = center
  · change center.Normal
    rw [← equality]
    exact candidate.property.1
  · let _normal := candidate.property.1
    have proper : candidate.val < center := lt_of_le_of_ne candidate.property.2 equality
    let closure := zjGrowthClosure (sylow : Subgroup GroupType) candidate.val
    have closure_normal : closure.Normal := zj_growth_closure_normal _ _
    have closure_le : closure ≤ center := zj_growth_closure_le_thompson_center prime prime_prime odd_prime
      stable self_centralizing sylow candidate.val proper
    have growth := (zj_growth_closure_class_two_properties prime prime_prime stable self_centralizing
      sylow candidate.val proper).1
    have cardinal_growth := subgroup_card_strict_mono growth
    have bound := optimal (⟨closure, closure_normal, closure_le⟩ : candidates)
    exact ((not_lt_of_ge bound) cardinal_growth).elim

end CFSG.SignalizerFunctor.Helpers
