module

public import CFSG.LocalAnalysis.SignalizerFunctor.HallConjugacy

public section

universe actorUniverse groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

open scoped Pointwise

theorem invariant_subgroup_pointwise_fixed
    {ActorType : Type actorUniverse} [Group ActorType]
    {GroupType : Type groupUniverse} [Group GroupType]
    [MulDistribMulAction ActorType GroupType]
    (subgroup : Subgroup GroupType)
    (invariant : ∀ actorElement : ActorType, ∀ element ∈ subgroup,
      actorElement • element ∈ subgroup) :
    ∀ actorElement : ActorType, actorElement • subgroup = subgroup := by
  intro actorElement
  rw [Subgroup.pointwise_smul_def]
  apply le_antisymm
  · rintro element ⟨representative, member, rfl⟩
    exact invariant actorElement representative member
  · intro element member
    exact ⟨actorElement⁻¹ • element, invariant actorElement⁻¹ element member,
      smul_inv_smul actorElement element⟩

theorem actor_conjugation_on_subgroups
    {ActorType : Type actorUniverse} [Group ActorType]
    {GroupType : Type groupUniverse} [Group GroupType]
    [MulDistribMulAction ActorType GroupType]
    (actorElement : ActorType) (groupElement : GroupType) (subgroup : Subgroup GroupType) :
    actorElement • (MulAut.conj groupElement • subgroup) =
      MulAut.conj (actorElement • groupElement) • (actorElement • subgroup) := by
  change (subgroup.map (MulAut.conj groupElement).toMonoidHom).map
      (MulDistribMulAction.toMonoidHom GroupType actorElement) =
    (subgroup.map (MulDistribMulAction.toMonoidHom GroupType actorElement)).map
      (MulAut.conj (actorElement • groupElement)).toMonoidHom
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext element
  change actorElement • (groupElement * element * groupElement⁻¹) =
    (actorElement • groupElement) * (actorElement • element) * (actorElement • groupElement)⁻¹
  rw [MulDistribMulAction.smul_mul, MulDistribMulAction.smul_mul, smul_inv']

theorem invariant_hall_subgroups_conjugate_by_fixed_element
    (prime : ℕ) (prime_prime : prime.Prime)
    (ActorType : Type actorUniverse) [Group ActorType]
    (actor_pgroup : IsPGroup prime ActorType)
    (GroupType : Type groupUniverse) [Group GroupType] [Finite GroupType]
    [Group.IsSolvable GroupType] [MulDistribMulAction ActorType GroupType]
    (coprime : Nat.Coprime prime (Nat.card GroupType))
    (primes : Set ℕ) (first second : Subgroup GroupType)
    (first_hall : IsHallSubgroup primes first) (second_hall : IsHallSubgroup primes second)
    (first_invariant : ∀ actorElement : ActorType, ∀ element ∈ first,
      actorElement • element ∈ first)
    (second_invariant : ∀ actorElement : ActorType, ∀ element ∈ second,
      actorElement • element ∈ second) :
    ∃ element : GroupType, conjugateSubgroup element first = second ∧
      ∀ actorElement : ActorType, actorElement • element = element := by
  let _groupAction : MulAction GroupType (Subgroup GroupType) :=
    MulAction.compHom (Subgroup GroupType) (MulAut.conj (G := GroupType))
  have compatible : ∀ actorElement : ActorType, ∀ groupElement : GroupType,
      ∀ subgroup : Subgroup GroupType,
      actorElement • (groupElement • subgroup) =
        (actorElement • groupElement) • (actorElement • subgroup) :=
    actor_conjugation_on_subgroups
  have conjugate : ∃ element : GroupType, element • first = second :=
    solvable_hall_subgroups_conjugate GroupType primes first second first_hall second_hall
  exact fixed_transporter_exists prime prime_prime ActorType actor_pgroup GroupType
    (Subgroup GroupType) compatible coprime first second
    (invariant_subgroup_pointwise_fixed first first_invariant)
    (invariant_subgroup_pointwise_fixed second second_invariant) conjugate

end CFSG.SignalizerFunctor.Helpers
