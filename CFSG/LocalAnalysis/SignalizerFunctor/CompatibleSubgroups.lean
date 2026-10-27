module

public import CFSG.Open.SignalizerFunctorTheoremMilestoneDefs

public section

open CFSG.Open

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType]

@[expose] def signalizerCompatible (prime rank : ℕ) (actor : Subgroup GroupType)
    (values : Subgroup GroupType → Subgroup GroupType) (target : Subgroup GroupType) : Prop :=
  actor ≤ Subgroup.normalizer (target : Set GroupType) ∧
    ∀ subgroup ∈ signalizerFunctorEk prime rank actor,
      target ⊓ Subgroup.centralizer (subgroup : Set GroupType) ≤ values subgroup

@[expose] def signalizerCommonFixed (prime rank : ℕ) (actor : Subgroup GroupType)
    (values : Subgroup GroupType → Subgroup GroupType) : Subgroup GroupType :=
  Subgroup.centralizer (actor : Set GroupType) ⊓
    ⨅ subgroup ∈ signalizerFunctorEk prime rank actor, values subgroup

theorem normalizer_inf_of_le (actor first second : Subgroup GroupType)
    (first_normalized : actor ≤ Subgroup.normalizer (first : Set GroupType))
    (second_normalized : actor ≤ Subgroup.normalizer (second : Set GroupType)) :
    actor ≤ Subgroup.normalizer ((first ⊓ second : Subgroup GroupType) : Set GroupType) := by
  apply Subgroup.le_normalizer_iff.mpr
  intro actorElement actor_member element member
  exact ⟨Subgroup.le_normalizer_iff.mp first_normalized actorElement actor_member
    element member.1, Subgroup.le_normalizer_iff.mp second_normalized actorElement
    actor_member element member.2⟩

theorem elementary_abelian_le_centralizer (prime : ℕ)
    (actor subgroup : Subgroup GroupType) (elementary : IsElemAbelian prime actor)
    (contained : subgroup ≤ actor) :
    actor ≤ Subgroup.centralizer (subgroup : Set GroupType) := by
  let := elementary.1
  intro actorElement actor_member
  apply Subgroup.mem_centralizer_iff.mpr
  intro subgroupElement subgroup_member
  exact congrArg (fun internal : actor => (internal : GroupType))
    (mul_comm' (⟨subgroupElement, contained subgroup_member⟩ : actor)
      (⟨actorElement, actor_member⟩ : actor))

theorem signalizer_compatible_inf (prime rank : ℕ) (actor : Subgroup GroupType)
    (values : Subgroup GroupType → Subgroup GroupType) (first second : Subgroup GroupType)
    (first_compatible : signalizerCompatible prime rank actor values first)
    (second_normalized : actor ≤ Subgroup.normalizer (second : Set GroupType)) :
    signalizerCompatible prime rank actor values (first ⊓ second) := by
  refine ⟨normalizer_inf_of_le actor first second first_compatible.1 second_normalized, ?_⟩
  intro subgroup member
  exact (inf_le_inf_right _ inf_le_left).trans (first_compatible.2 subgroup member)

theorem signalizer_compatible_of_le (prime rank : ℕ) (actor : Subgroup GroupType)
    (values : Subgroup GroupType → Subgroup GroupType) {larger smaller : Subgroup GroupType}
    (larger_compatible : signalizerCompatible prime rank actor values larger)
    (contained : smaller ≤ larger)
    (smaller_normalized : actor ≤ Subgroup.normalizer (smaller : Set GroupType)) :
    signalizerCompatible prime rank actor values smaller := by
  refine ⟨smaller_normalized, ?_⟩
  intro subgroup member
  exact (inf_le_inf_right _ contained).trans (larger_compatible.2 subgroup member)

theorem signalizer_value_compatible (prime rank : ℕ) (actor : Subgroup GroupType)
    (values : Subgroup GroupType → Subgroup GroupType)
    (invariant : ∀ subgroup ∈ signalizerFunctorEk prime rank actor,
      actor ≤ Subgroup.normalizer (values subgroup : Set GroupType))
    (balanced : ∀ subgroup ∈ signalizerFunctorEk prime rank actor,
      ∀ other ∈ signalizerFunctorEk prime rank actor,
        values subgroup ⊓ Subgroup.centralizer (other : Set GroupType) ≤ values other)
    {subgroup : Subgroup GroupType} (member : subgroup ∈ signalizerFunctorEk prime rank actor) :
    signalizerCompatible prime rank actor values (values subgroup) :=
  ⟨invariant subgroup member, balanced subgroup member⟩

theorem signalizer_value_common_fixed (prime rank : ℕ) (actor : Subgroup GroupType)
    (values : Subgroup GroupType → Subgroup GroupType)
    (balanced : ∀ subgroup ∈ signalizerFunctorEk prime rank actor,
      ∀ other ∈ signalizerFunctorEk prime rank actor,
        values subgroup ⊓ Subgroup.centralizer (other : Set GroupType) ≤ values other)
    {subgroup : Subgroup GroupType} (member : subgroup ∈ signalizerFunctorEk prime rank actor) :
    values subgroup ⊓ Subgroup.centralizer (actor : Set GroupType) =
      signalizerCommonFixed prime rank actor values := by
  apply le_antisymm
  · refine le_inf inf_le_right ?_
    apply le_iInf
    intro other
    apply le_iInf
    intro other_member
    exact (inf_le_inf_left _ (Subgroup.centralizer_le other_member.1)).trans
      (balanced subgroup member other other_member)
  · exact le_inf ((inf_le_right.trans (iInf_le _ subgroup)).trans (iInf_le _ member))
      inf_le_left

theorem signalizer_compatible_map (prime rank : ℕ) (actor : Subgroup GroupType)
    (values : Subgroup GroupType → Subgroup GroupType) (target : Subgroup GroupType)
    (equiv : GroupType ≃* GroupType)
    (actor_preserved : actor.map equiv.toMonoidHom = actor)
    (fixed_preserved : ∀ subgroup ∈ signalizerFunctorEk prime rank actor,
      (Subgroup.centralizer (subgroup : Set GroupType)).map equiv.toMonoidHom =
        Subgroup.centralizer (subgroup : Set GroupType))
    (values_preserved : ∀ subgroup ∈ signalizerFunctorEk prime rank actor,
      (values subgroup).map equiv.toMonoidHom = values subgroup)
    (compatible : signalizerCompatible prime rank actor values target) :
    signalizerCompatible prime rank actor values (target.map equiv.toMonoidHom) := by
  refine ⟨?_, ?_⟩
  · have normalized := Subgroup.map_mono (f := equiv.toMonoidHom) compatible.1
    rwa [actor_preserved, Subgroup.map_equiv_normalizer_eq] at normalized
  · intro subgroup member
    have bound := Subgroup.map_mono (f := equiv.toMonoidHom)
      (compatible.2 subgroup member)
    rwa [Subgroup.map_inf _ _ _ equiv.injective, fixed_preserved subgroup member,
      values_preserved subgroup member] at bound

theorem signalizer_compatible_conjugate (prime rank : ℕ) (actor : Subgroup GroupType)
    (values : Subgroup GroupType → Subgroup GroupType) (target : Subgroup GroupType)
    (compatible : signalizerCompatible prime rank actor values target)
    (element : signalizerCommonFixed prime rank actor values) :
    signalizerCompatible prime rank actor values
      (target.map (MulAut.conj element.val).toMonoidHom) := by
  apply signalizer_compatible_map prime rank actor values target (MulAut.conj element.val)
    _ _ _ compatible
  · exact Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (Subgroup.centralizer_le_normalizer _ element.property.1)
  · intro subgroup member
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mp
    apply Subgroup.le_normalizer
    exact Subgroup.centralizer_le member.1 element.property.1
  · intro subgroup member
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mp
    apply Subgroup.le_normalizer
    have all_values : ∀ _ : subgroup ∈ signalizerFunctorEk prime rank actor,
        element.val ∈ values subgroup :=
      Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp element.property.2 subgroup)
    exact all_values member

end CFSG.SignalizerFunctor.Helpers
