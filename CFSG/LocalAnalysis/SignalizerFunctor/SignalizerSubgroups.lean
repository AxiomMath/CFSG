module

public import CFSG.LocalAnalysis.SignalizerFunctor.HallTransport
public import CFSG.LocalAnalysis.SignalizerFunctor.CentralizerImages
public import CFSG.LocalAnalysis.SignalizerFunctor.SignalizerSubgroupIndices

public section

open CFSG.Open

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType]

theorem signalizer_subgroup_compatible_iff (prime rank : ℕ)
    (actor ambient : Subgroup GroupType) (contained : actor ≤ ambient)
    (values : Subgroup GroupType → Subgroup GroupType) (target : Subgroup ambient) :
    signalizerCompatible prime rank (actor.subgroupOf ambient)
      (signalizerSubgroupValues ambient values) target ↔
      signalizerCompatible prime rank actor values (target.map ambient.subtype) := by
  constructor
  · intro compatible
    refine ⟨?_, ?_⟩
    · have normalized := normalizer_image_le ambient.subtype (actor.subgroupOf ambient)
        target compatible.1
      rwa [subgroup_actor_map actor ambient contained] at normalized
    · intro selected member
      have internal_member := signalizer_ambient_index_member prime rank actor ambient contained
        selected member
      have bounds := Subgroup.map_mono (f := ambient.subtype)
        (compatible.2 (selected.subgroupOf ambient) internal_member)
      rw [centralizer_image_of_injective ambient.subtype ambient.subtype_injective,
        subgroup_actor_map selected ambient (member.1.trans contained),
        signalizer_subgroup_value_at_ambient_index ambient selected values (member.1.trans contained),
        Subgroup.subgroupOf_map_subtype] at bounds
      exact bounds.trans inf_le_left
  · intro compatible
    refine ⟨?_, ?_⟩
    · have normalized := normalizer_comap_le ambient.subtype (actor.subgroupOf ambient)
        (target.map ambient.subtype)
        (by rw [subgroup_actor_map actor ambient contained]; exact compatible.1)
      rwa [Subgroup.comap_map_eq_self_of_injective ambient.subtype_injective] at normalized
    · intro selected member
      apply (Subgroup.map_le_map_iff_of_injective ambient.subtype_injective).mp
      rw [centralizer_image_of_injective ambient.subtype ambient.subtype_injective,
        signalizer_subgroup_value_map]
      exact le_inf
        (compatible.2 (selected.map ambient.subtype)
          (signalizer_subgroup_index_member prime rank actor ambient contained selected member))
        (inf_le_left.trans (Subgroup.map_subtype_le target))

theorem signalizer_subgroup_properties [Finite GroupType] (prime rank : ℕ)
    (actor ambient : Subgroup GroupType) (contained : actor ≤ ambient)
    (values : Subgroup GroupType → Subgroup GroupType)
    (central : ∀ subgroup ∈ signalizerFunctorEk prime rank actor,
      values subgroup ≤ Subgroup.centralizer (subgroup : Set GroupType))
    (coprime : ∀ subgroup ∈ signalizerFunctorEk prime rank actor,
      Nat.Coprime prime (Nat.card (values subgroup)))
    (normalized : ∀ subgroup ∈ signalizerFunctorEk prime rank actor,
      actor ≤ Subgroup.normalizer (values subgroup : Set GroupType))
    (balanced : ∀ subgroup ∈ signalizerFunctorEk prime rank actor,
      ∀ other ∈ signalizerFunctorEk prime rank actor,
        values subgroup ⊓ Subgroup.centralizer (other : Set GroupType) ≤ values other) :
    (∀ subgroup ∈ signalizerFunctorEk prime rank (actor.subgroupOf ambient),
      signalizerSubgroupValues ambient values subgroup ≤
        Subgroup.centralizer (subgroup : Set ambient) ∧
      Nat.Coprime prime (Nat.card (signalizerSubgroupValues ambient values subgroup)) ∧
      actor.subgroupOf ambient ≤ Subgroup.normalizer
        (signalizerSubgroupValues ambient values subgroup : Set ambient)) ∧
    (∀ subgroup ∈ signalizerFunctorEk prime rank (actor.subgroupOf ambient),
      ∀ other ∈ signalizerFunctorEk prime rank (actor.subgroupOf ambient),
        signalizerSubgroupValues ambient values subgroup ⊓
          Subgroup.centralizer (other : Set ambient) ≤
            signalizerSubgroupValues ambient values other) := by
  have compatible : ∀ subgroup ∈ signalizerFunctorEk prime rank (actor.subgroupOf ambient),
      signalizerCompatible prime rank (actor.subgroupOf ambient)
        (signalizerSubgroupValues ambient values) (signalizerSubgroupValues ambient values subgroup) := by
    intro subgroup member
    apply (signalizer_subgroup_compatible_iff prime rank actor ambient contained values _).mpr
    rw [signalizer_subgroup_value_map]
    exact signalizer_compatible_inf prime rank actor values _ ambient
      (signalizer_value_compatible prime rank actor values normalized balanced
        (signalizer_subgroup_index_member prime rank actor ambient contained subgroup member))
      (contained.trans Subgroup.le_normalizer)
  refine ⟨?_, fun subgroup member => (compatible subgroup member).2⟩
  intro subgroup member
  refine ⟨?_, (coprime (subgroup.map ambient.subtype)
    (signalizer_subgroup_index_member prime rank actor ambient contained subgroup member)).of_dvd_right
      (Subgroup.card_comap_dvd_of_injective _ ambient.subtype ambient.subtype_injective),
    (compatible subgroup member).1⟩
  intro element element_member
  apply Subgroup.mem_centralizer_iff.mpr
  intro actorElement actor_member
  apply Subtype.ext
  exact Subgroup.mem_centralizer_iff.mp
    (central (subgroup.map ambient.subtype)
      (signalizer_subgroup_index_member prime rank actor ambient contained subgroup member)
      element_member) actorElement.val (Subgroup.mem_map_of_mem ambient.subtype actor_member)

theorem signalizer_subgroup_solvable (prime rank : ℕ)
    (actor ambient : Subgroup GroupType) (contained : actor ≤ ambient)
    (values : Subgroup GroupType → Subgroup GroupType)
    (solvable : ∀ subgroup ∈ signalizerFunctorEk prime rank actor,
      Group.IsSolvable (values subgroup)) :
    ∀ subgroup ∈ signalizerFunctorEk prime rank (actor.subgroupOf ambient),
      Group.IsSolvable (signalizerSubgroupValues ambient values subgroup) := by
  intro subgroup member
  let := solvable (subgroup.map ambient.subtype)
    (signalizer_subgroup_index_member prime rank actor ambient contained subgroup member)
  let inclusion : signalizerSubgroupValues ambient values subgroup →*
      values (subgroup.map ambient.subtype) :=
    (ambient.subtype.comp (signalizerSubgroupValues ambient values subgroup).subtype).codRestrict _
      (fun element => element.property)
  have injective : Function.Injective inclusion := by
    intro first second equality
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun element : values (subgroup.map ambient.subtype) => element.val) equality
  exact Group.isSolvable_of_isSolvable_injective injective

theorem signalizer_subgroup_supported (prime rank : ℕ)
    (actor ambient : Subgroup GroupType) (contained : actor ≤ ambient)
    (values : Subgroup GroupType → Subgroup GroupType) (primes : Set ℕ)
    (supported : ∀ subgroup ∈ signalizerFunctorEk prime rank actor,
      primeSupported primes (Nat.card (values subgroup))) :
    ∀ subgroup ∈ signalizerFunctorEk prime rank (actor.subgroupOf ambient),
      primeSupported primes (Nat.card (signalizerSubgroupValues ambient values subgroup)) := by
  intro subgroup member
  exact prime_supported_of_dvd primes
    (supported _ (signalizer_subgroup_index_member prime rank actor ambient contained subgroup member))
    (Subgroup.card_comap_dvd_of_injective _ ambient.subtype ambient.subtype_injective)

theorem signalizer_subgroup_completion (prime rank : ℕ)
    (actor ambient : Subgroup GroupType) (contained : actor ≤ ambient)
    (values : Subgroup GroupType → Subgroup GroupType) :
    (⨆ selected ∈ signalizerFunctorEk prime rank (actor.subgroupOf ambient),
      signalizerSubgroupValues ambient values selected).map ambient.subtype =
    ⨆ selected ∈ signalizerFunctorEk prime rank actor,
      signalizerRestriction values ambient selected := by
  rw [Subgroup.map_iSup]
  simp_rw [Subgroup.map_iSup, signalizer_subgroup_value_map]
  apply le_antisymm
  · apply iSup_le
    intro selected
    apply iSup_le
    intro member
    exact signalizer_value_le_completion prime rank actor (signalizerRestriction values ambient)
      (signalizer_subgroup_index_member prime rank actor ambient contained selected member)
  · apply iSup_le
    intro selected
    apply iSup_le
    intro member
    have selected_map := subgroup_actor_map selected ambient (member.1.trans contained)
    conv_lhs => rw [← selected_map]
    exact le_iSup_of_le (selected.subgroupOf ambient) (le_iSup_of_le
      (signalizer_ambient_index_member prime rank actor ambient contained selected member) le_rfl)

theorem signalizer_subgroup_completion_compatible_iff (prime rank : ℕ)
    (actor ambient : Subgroup GroupType) (contained : actor ≤ ambient)
    (values : Subgroup GroupType → Subgroup GroupType) :
    signalizerCompatible prime rank (actor.subgroupOf ambient)
      (signalizerSubgroupValues ambient values)
      (⨆ selected ∈ signalizerFunctorEk prime rank (actor.subgroupOf ambient),
        signalizerSubgroupValues ambient values selected) ↔
    signalizerCompatible prime rank actor values
      (⨆ selected ∈ signalizerFunctorEk prime rank actor,
        signalizerRestriction values ambient selected) := by
  rw [signalizer_subgroup_compatible_iff prime rank actor ambient contained values,
    signalizer_subgroup_completion prime rank actor ambient contained values]

end CFSG.SignalizerFunctor.Helpers
