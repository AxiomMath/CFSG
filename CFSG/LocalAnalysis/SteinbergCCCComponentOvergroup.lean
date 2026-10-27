module

public import CFSG.Foundations.Basic

public section

namespace CFSG.LocalAnalysis

open Subgroup

theorem Ccomponent_overgroup {G : Type*} [Group G] {L H : Subgroup G} (hL : IsCComponent L)
    (hLH : L ≤ H) : IsCComponent (L.subgroupOf H) := by
  obtain ⟨hL1, hLp, hLs, hLmin⟩ := hL
  have hinj := H.subtype_injective
  have hmapL : (L.subgroupOf H).map H.subtype = L := map_subgroupOf_eq_of_le hLH
  refine ⟨fun h => hL1 (by rw [← hmapL, h, Subgroup.map_bot]), ?_, hLs.subgroupOf,
    fun K hK hK1 hKp hKs => ?_⟩
  · apply map_injective hinj
    rw [map_commutator, hmapL, hLp]
  · have hK'L : K.map H.subtype < L := by
      rw [← hmapL]
      exact (map_lt_map_iff_of_injective hinj).mpr hK
    have hK'1 : K.map H.subtype ≠ ⊥ := fun h =>
      hK1 ((map_eq_bot_iff_of_injective K hinj).mp h)
    have hK'p : ⁅K.map H.subtype, K.map H.subtype⁆ = K.map H.subtype := by
      rw [← map_commutator, hKp]
    have hsub : ((K.map H.subtype).subgroupOf L).IsSubnormal := by
      have h := hKs.comap (Subgroup.inclusion hLH)
      convert h using 1
      ext x
      rw [mem_subgroupOf, mem_comap, mem_map]
      constructor
      · rintro ⟨y, hy, hyx⟩
        have : Subgroup.inclusion hLH x = y := Subtype.ext hyx.symm
        rw [this]
        exact hy
      · intro hx
        exact ⟨_, hx, rfl⟩
    exact hLmin _ hK'L hK'1 hK'p (hsub.trans hK'L.le hLs)

end CFSG.LocalAnalysis
