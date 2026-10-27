module

public import CFSG.LocalAnalysis.SignalizerFunctor.AxiomaticZJNormality
import CFSG.LocalAnalysis.SignalizerFunctor.ThompsonCanonical
import CFSG.Foundations.MaxOrderThompsonImage
import CFSG.GroupTheory.SylowNaturalCharacteristic

public section

universe groupUniverse imageUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]

omit [Finite GroupType] in
theorem embedded_order_thompson_center_map_of_injective
    {ImageType : Type imageUniverse} [Group ImageType]
    (homomorphism : GroupType →* ImageType) (injective : Function.Injective homomorphism)
    (parent : Subgroup GroupType) :
    (embeddedOrderThompsonCenter parent).map homomorphism =
      embeddedOrderThompsonCenter (parent.map homomorphism) := by
  unfold embeddedOrderThompsonCenter
  rw [order_thompson_center_eq_maxCardZJ, order_thompson_center_eq_maxCardZJ]
  exact CFSG.map_maxCardZJ_map_subtype_of_injective homomorphism parent
    (injective.comp parent.subtype_injective)

theorem normal_embedded_thompson_center_characteristic (prime : ℕ) (prime_prime : prime.Prime)
    (sylow : Sylow prime GroupType)
    (normal : (embeddedOrderThompsonCenter (sylow : Subgroup GroupType)).Normal) :
    (embeddedOrderThompsonCenter (sylow : Subgroup GroupType)).Characteristic :=
  have : Fact prime.Prime := ⟨prime_prime⟩
  have := normal
  CFSG.characteristic_of_normal_of_map_mulEquiv (fun target => embeddedOrderThompsonCenter target)
    (fun automorphism target => embedded_order_thompson_center_map_of_injective
      automorphism.toMonoidHom automorphism.injective target) sylow

theorem axiomatic_zj_characteristic (prime : ℕ) (prime_prime : prime.Prime) (odd_prime : prime ≠ 2)
    (stable : normalPSubgroupActionsStable prime GroupType)
    (self_centralizing : Subgroup.centralizer
      (primeSetCore (GroupType := GroupType) {prime} : Set GroupType) ≤ primeSetCore {prime})
    (sylow : Sylow prime GroupType) :
    (embeddedOrderThompsonCenter (sylow : Subgroup GroupType)).Characteristic :=
  normal_embedded_thompson_center_characteristic prime prime_prime sylow
    (axiomatic_zj_normality prime prime_prime odd_prime stable self_centralizing sylow)

end CFSG.SignalizerFunctor.Helpers
