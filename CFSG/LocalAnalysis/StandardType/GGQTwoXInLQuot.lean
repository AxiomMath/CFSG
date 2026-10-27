module

public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
public import CFSG.LocalAnalysis.StandardType.GGSkeleton
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4UGroup
public import CFSG.LocalAnalysis.StandardType.GGSecFiveQTwoCompat
public import CFSG.LocalAnalysis.StandardType.GGSixLSixSevenE6Components

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem isComponentOf_map_mk_center_centralizer {G : Type*} [Group G] {H L : Subgroup G}
    {x : G} (hL : IsComponentOf L (Subgroup.centralizer {x})) (hLH : L ≤ H) (hx : x ∈ H) :
    IsComponentOf ((L.subgroupOf H).map (QuotientGroup.mk' (Subgroup.center ↥H)))
      (Subgroup.centralizer {QuotientGroup.mk' (Subgroup.center ↥H) (⟨x, hx⟩ : ↥H)}) := by
  have hcomp : IsComponentOf L (Subgroup.centralizer ({x} : Set G) ⊓ H) :=
    ggIsComponentOf_inf_of_le hL hLH
  have hsub : IsComponentOf (L.subgroupOf H)
      ((Subgroup.centralizer ({x} : Set G) ⊓ H).subgroupOf H) :=
    ggIsComponentOf_subgroupOf_of_le H hLH hcomp
  have hcent : ((Subgroup.centralizer ({x} : Set G) ⊓ H).subgroupOf H) =
      Subgroup.centralizer ({(⟨x, hx⟩ : ↥H)} : Set ↥H) := by
    ext y
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨h, -⟩
      exact Subtype.ext h
    · intro h
      exact ⟨congrArg Subtype.val h, y.2⟩
  have hJ : CFSG.Open.IsComponentOf (L.subgroupOf H)
      (Subgroup.centralizer ({(⟨x, hx⟩ : ↥H)} : Set ↥H)) := by
    rw [← hcent]
    exact (CFSG.Assembly.isComponentOf_iff_open).mp hsub
  have hmap := TableCRes.isComponentOf_map_centralizer_central (G := ↥H)
    (Z := Subgroup.center ↥H) (le_refl (Subgroup.center ↥H))
    ({(⟨x, hx⟩ : ↥H)} : Set ↥H) hJ
  rw [Set.image_singleton] at hmap
  exact (CFSG.Assembly.isComponentOf_iff_open).mpr hmap

theorem GGConfig.isComponentOf_map_ggG0_center {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    (hxL : x ∈ L) :
    IsComponentOf ((L.subgroupOf (ggG0 p B x L D J)).map
        (QuotientGroup.mk' (Subgroup.center ↥(ggG0 p B x L D J))))
      (Subgroup.centralizer
        {QuotientGroup.mk' (Subgroup.center ↥(ggG0 p B x L D J))
          (⟨x, le_ggG0_left p B x L D J hxL⟩ : ↥(ggG0 p B x L D J))}) :=
  isComponentOf_map_mk_center_centralizer hcfg.1.2.2.2.2.2.2.1.2.2.2.1
    (le_ggG0_left p B x L D J) _

end CFSG.StandardType

end
