module

public import CFSG.LocalAnalysis.SignalizerFunctor.FixedTransporter

public section

universe actorUniverse groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

open scoped Pointwise

theorem actor_conjugation_on_sylows
    {ActorType : Type actorUniverse} [Group ActorType]
    {GroupType : Type groupUniverse} [Group GroupType]
    [MulDistribMulAction ActorType GroupType]
    (prime : ℕ) (actorElement : ActorType) (groupElement : GroupType)
    (sylow : Sylow prime GroupType) :
    actorElement • (groupElement • sylow) =
      (actorElement • groupElement) • (actorElement • sylow) := by
  apply Sylow.ext
  change ((sylow : Subgroup GroupType).map (MulAut.conj groupElement).toMonoidHom).map
      (MulDistribMulAction.toMonoidHom GroupType actorElement) =
    ((sylow : Subgroup GroupType).map
      (MulDistribMulAction.toMonoidHom GroupType actorElement)).map
        (MulAut.conj (actorElement • groupElement)).toMonoidHom
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext element
  change actorElement • (groupElement * element * groupElement⁻¹) =
    (actorElement • groupElement) * (actorElement • element) *
      (actorElement • groupElement)⁻¹
  rw [MulDistribMulAction.smul_mul, MulDistribMulAction.smul_mul, smul_inv']

theorem invariant_sylows_conjugate_by_fixed_element
    (prime sylowPrime : ℕ) (prime_prime : prime.Prime)
    (sylowPrime_prime : sylowPrime.Prime)
    (ActorType : Type actorUniverse) [Group ActorType]
    (actor_pgroup : IsPGroup prime ActorType)
    (GroupType : Type groupUniverse) [Group GroupType] [Finite GroupType]
    [MulDistribMulAction ActorType GroupType]
    (coprime : Nat.Coprime prime (Nat.card GroupType))
    (first second : Sylow sylowPrime GroupType)
    (first_fixed : ∀ actorElement : ActorType, actorElement • first = first)
    (second_fixed : ∀ actorElement : ActorType, actorElement • second = second) :
    ∃ groupElement : GroupType, groupElement • first = second ∧
      ∀ actorElement : ActorType, actorElement • groupElement = groupElement := by
  let : Fact sylowPrime.Prime := ⟨sylowPrime_prime⟩
  exact fixed_transporter_exists prime prime_prime ActorType actor_pgroup GroupType
    (Sylow sylowPrime GroupType) (actor_conjugation_on_sylows sylowPrime)
    coprime first second first_fixed second_fixed
    (MulAction.exists_smul_eq GroupType first second)

end CFSG.SignalizerFunctor.Helpers
