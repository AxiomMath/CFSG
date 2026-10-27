module

public import CFSG.Quasithin.Vol2.GoldschmidtSp4C2GrpCoord

public section

namespace CFSG.Quasithin.SimsG45

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open CFSG.QuasithinUnique

theorem mem_centralizer_iff_map_mem_antiUnipotent {G : Type*} [Group G] {F : Type} [Field F]
    [CharP F 2] {S : Subgroup G} (e : ↥S ≃* antiSp F) {x : G} (hx : x ∈ S) {β γ : F}
    (hβ : β ≠ 0) (hγ : γ ≠ 0) (hex : e ⟨x, hx⟩ = uElt 0 β γ 0) (s : ↥S) :
    (s : G) ∈ Subgroup.centralizer ({x} : Set G) ↔ e s ∈ antiUnipotent F := by
  have key : (s : G) * x = x * s ↔ e s * uElt 0 β γ 0 = uElt 0 β γ 0 * e s := by
    rw [← hex, ← map_mul, ← map_mul, e.injective.eq_iff]
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  rw [Subgroup.mem_centralizer_singleton_iff, key]
  exact ⟨Ch3E213M.Sp4C2.mem_unipotent_of_comm hβ hγ,
    fun hu => (antiUnipotentCenter_comm ⟨β, γ, rfl⟩ hu).symm⟩

theorem subgroupOf_centralizer_inf_eq_comap {G : Type*} [Group G] {F : Type} [Field F]
    [CharP F 2] {S : Subgroup G} (e : ↥S ≃* antiSp F) {x : G} (hx : x ∈ S) {β γ : F}
    (hβ : β ≠ 0) (hγ : γ ≠ 0) (hex : e ⟨x, hx⟩ = uElt 0 β γ 0) :
    (Subgroup.centralizer ({x} : Set G) ⊓ S).subgroupOf S =
      (antiUnipotent F).comap (e : ↥S →* antiSp F) := by
  ext s
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_comap,
    mem_centralizer_iff_map_mem_antiUnipotent e hx hβ hγ hex s]
  exact ⟨fun h => h.1, fun h => ⟨h, s.2⟩⟩

theorem isSylowTwoOf_centralizer_of_mulEquiv {G : Type*} [Group G] {F : Type} [Field F]
    [Finite F] [CharP F 2] (S : Subgroup G) (e : ↥S ≃* antiSp F) {x : G} (hx : x ∈ S)
    {β γ : F} (hβ : β ≠ 0) (hγ : γ ≠ 0) (hex : e ⟨x, hx⟩ = uElt 0 β γ 0) :
    IsSylowTwoOf (Subgroup.centralizer ({x} : Set G) ⊓ S) S := by
  obtain ⟨-, hU2, hUodd⟩ := (Setup.X7b.card_and_isSylowTwoOf_antiUnipotent (K := F)).2
  refine ⟨inf_le_right, ?_, ?_⟩
  · have hmem : ∀ a : ↥(Subgroup.centralizer ({x} : Set G) ⊓ S),
        e ⟨a, a.2.2⟩ ∈ antiUnipotent F := fun a =>
      (mem_centralizer_iff_map_mem_antiUnipotent e hx hβ hγ hex ⟨a, a.2.2⟩).mp a.2.1
    refine hU2.of_injective
      (((e : ↥S →* antiSp F).comp (Subgroup.inclusion inf_le_right)).codRestrict
        (antiUnipotent F) hmem) fun a b h => ?_
    exact Subgroup.inclusion_injective _ (e.injective (congrArg Subtype.val h))
  · rw [subgroupOf_centralizer_inf_eq_comap e hx hβ hγ hex,
      Subgroup.index_comap_of_surjective (antiUnipotent F) e.surjective]
    rwa [show ((antiUnipotent F).subgroupOf ⊤).index = (antiUnipotent F).index from
      Subgroup.relIndex_top_right _] at hUodd

end CFSG.Quasithin.SimsG45
