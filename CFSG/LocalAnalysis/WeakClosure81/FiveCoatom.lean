module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Quasithin.Background.B6Defs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin Subgroup

variable {G : Type} [Group G]

theorem isCoatom_subgroupOf {H N : Subgroup G} (h : IsMaxSubgroupIn H N) :
    IsCoatom (N.subgroupOf H) := by
  have hNH : N ≤ H := h.1.le
  refine ⟨fun htop => absurd (Subgroup.subgroupOf_eq_top.mp htop) (not_le_of_gt h.1),
    fun K' hK' => ?_⟩
  have hmap : N < K'.map H.subtype := by
    have := (Subgroup.map_lt_map_iff_of_injective H.subtype_injective).mpr hK'
    rwa [Subgroup.map_subgroupOf_eq_of_le hNH] at this
  have hK : K'.map H.subtype = H := h.2 _ hmap (by
    rintro _ ⟨x, -, rfl⟩
    exact x.2)
  have h1 : K' = (K'.map H.subtype).comap H.subtype :=
    (Subgroup.comap_map_eq_self_of_injective H.subtype_injective K').symm
  rw [h1, hK]
  exact Subgroup.subgroupOf_self H

theorem isMaxSubgroupIn_map_subtype {H : Subgroup G} {N' : Subgroup H} (h : IsCoatom N') :
    IsMaxSubgroupIn H (N'.map H.subtype) := by
  refine ⟨?_, fun K hK hKH => ?_⟩
  · refine lt_of_le_of_ne (by rintro _ ⟨x, -, rfl⟩; exact x.2) fun heq => ?_
    apply h.1
    have h1 : N' = (N'.map H.subtype).comap H.subtype :=
      (Subgroup.comap_map_eq_self_of_injective H.subtype_injective N').symm
    rw [h1, heq]
    exact Subgroup.subgroupOf_self H
  · have hlt : N' < K.subgroupOf H := by
      have h1 := (Subgroup.map_lt_map_iff_of_injective H.subtype_injective
        (H := N') (K := K.subgroupOf H))
      rw [Subgroup.map_subgroupOf_eq_of_le hKH] at h1
      exact h1.mp hK
    have := h.2 _ hlt
    have h2 : K = (K.subgroupOf H).map H.subtype :=
      (Subgroup.map_subgroupOf_eq_of_le hKH).symm
    rw [h2, this, Subgroup.map_top, Subgroup.range_subtype]

end CFSG.LocalAnalysis.WeakClosure81
