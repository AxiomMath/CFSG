module

public import CFSG.Foundations.Basic

public section

namespace CFSG.Quasithin.SteinbergBM

open Subgroup

theorem Ccomponent_subnormal_lift {G : Type*} [Group G] {H : Subgroup G} (hH : H.IsSubnormal)
    {L : Subgroup H} (hL : CFSG.IsCComponent L) : CFSG.IsCComponent (L.map H.subtype) := by
  obtain ⟨hL1, hLp, hLs, hLmin⟩ := hL
  have hinj := H.subtype_injective
  refine ⟨fun h => hL1 ?_, by rw [← map_commutator, hLp], hLs.trans' hH,
    fun K hK hK1 hKp hKs => ?_⟩
  · rw [← Subgroup.map_bot H.subtype] at h
    exact map_injective hinj h
  ·
    have hKH : K ≤ H := hK.le.trans (map_subtype_le L)
    have hmapK : (K.subgroupOf H).map H.subtype = K := map_subgroupOf_eq_of_le hKH
    refine hLmin (K.subgroupOf H) ?_ ?_ ?_ hKs.subgroupOf
    · rw [← map_lt_map_iff_of_injective hinj, hmapK]
      exact hK
    · intro h
      apply hK1
      rw [← hmapK, h, Subgroup.map_bot]
    · apply map_injective hinj
      rw [map_commutator, hmapK, hKp]

end CFSG.Quasithin.SteinbergBM
