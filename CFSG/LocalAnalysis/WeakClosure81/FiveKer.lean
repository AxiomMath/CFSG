module

public import CFSG.LocalAnalysis.WeakClosure81.SevenThree

public section

namespace CFSG.LocalAnalysis.WeakClosure81

variable {G : Type} [Group G]

theorem kerMOf_le_group (M H : Subgroup G) : kerMOf M H ≤ H :=
  Subgroup.map_subtype_le _

theorem kerMOf_le_left (M H : Subgroup G) : kerMOf M H ≤ M := by
  rintro _ ⟨y, hy, rfl⟩
  exact Subgroup.normalCore_le (M.subgroupOf H) hy

theorem subgroupOf_kerMOf (M H : Subgroup G) :
    (kerMOf M H).subgroupOf H = (M.subgroupOf H).normalCore :=
  Subgroup.comap_map_eq_self_of_injective H.subtype_injective _

theorem normal_subgroupOf_kerMOf (M H : Subgroup G) : ((kerMOf M H).subgroupOf H).Normal := by
  rw [subgroupOf_kerMOf]
  exact Subgroup.normalCore_normal _

theorem conj_mem_kerMOf {M H : Subgroup G} {g x : G} (hg : g ∈ H) (hx : x ∈ kerMOf M H) :
    g * x * g⁻¹ ∈ kerMOf M H :=
  (Subgroup.normal_subgroupOf_iff (kerMOf_le_group M H)).1 (normal_subgroupOf_kerMOf M H) x g hx hg

theorem le_kerMOf_of_normal {M H N : Subgroup G} (hNH : N ≤ H) (hN : (N.subgroupOf H).Normal)
    (hNM : N ≤ M) : N ≤ kerMOf M H := by
  have h1 : N.subgroupOf H ≤ (M.subgroupOf H).normalCore :=
    (Subgroup.normal_le_normalCore (hN := hN)).2 (fun x hx => hNM hx)
  calc N = (N.subgroupOf H).map H.subtype := (Subgroup.map_subgroupOf_eq_of_le hNH).symm
    _ ≤ kerMOf M H := Subgroup.map_mono h1

theorem mem_kerMOf_iff {M H : Subgroup G} {x : G} :
    x ∈ kerMOf M H ↔ x ∈ H ∧ ∀ g ∈ H, g * x * g⁻¹ ∈ M := by
  refine ⟨fun hx => ⟨kerMOf_le_group M H hx, fun g hg => kerMOf_le_left M H
    (conj_mem_kerMOf hg hx)⟩, fun ⟨hxH, hx⟩ => ?_⟩
  refine ⟨⟨x, hxH⟩, ?_, rfl⟩
  intro b
  exact hx b b.2

end CFSG.LocalAnalysis.WeakClosure81
