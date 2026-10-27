module

public import CFSG.Quasithin.EmptyFaithful.S152NWreath
public import CFSG.Quasithin.Background.A4Four

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

namespace S152N

theorem pCore_le_subgroupOf {H T : Subgroup G} (hT : IsSylowTwoOf T H) :
    CFSG.Open.pCore 2 ↥H ≤ T.subgroupOf H := by
  intro x hx
  have : (x : G) ∈ pCoreOf 2 H := ⟨x, hx, rfl⟩
  exact B6.pCoreOf_two_le_of_isSylowTwoOf hT this

theorem ker_mk_le_subgroupOf {H T : Subgroup G} (hT : IsSylowTwoOf T H) :
    (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H)).ker ≤ T.subgroupOf H := by
  rw [QuotientGroup.ker_mk']
  exact pCore_le_subgroupOf hT

theorem isSylowTwoOf_image {H T : Subgroup G} (hT : IsSylowTwoOf T H) (φ : OTwoQuot H ≃* W3) :
    IsSylowTwoOf
      (((T.subgroupOf H).map (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H))).map
        (φ : OTwoQuot H →* W3)) ⊤ := by
  refine ⟨le_top, ?_, ?_⟩
  · exact IsPGroup.map (IsPGroup.map (A4.isPGroup_subgroupOf_of_le hT.1 hT.2.1) _) _
  · have h1 : ((((T.subgroupOf H).map (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H))).map
        (φ : OTwoQuot H →* W3)).subgroupOf ⊤).index =
        (((T.subgroupOf H).map (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H))).map
          (φ : OTwoQuot H →* W3)).index :=
      Subgroup.relIndex_top_right _
    rw [h1, Subgroup.index_map_equiv _ φ,
      Subgroup.index_map_eq _ (QuotientGroup.mk'_surjective _) (ker_mk_le_subgroupOf hT)]
    exact hT.2.2

theorem relIndex_eq_nine {H T : Subgroup G} (hT : IsSylowTwoOf T H) (φ : OTwoQuot H ≃* W3) :
    T.relIndex H = 9 := by
  have h := W3.index_eq_nine (isSylowTwoOf_image hT φ)
  rw [Subgroup.index_map_equiv _ φ,
    Subgroup.index_map_eq _ (QuotientGroup.mk'_surjective _) (ker_mk_le_subgroupOf hT)] at h
  exact h

theorem eq_or_eq_of_le {H T : Subgroup G} (hT : IsSylowTwoOf T H) (φ : OTwoQuot H ≃* W3)
    {Y : Subgroup G} (hTY : T ≤ Y) (hYH : Y ≤ H) : Y = T ∨ Y = H := by
  have hker := ker_mk_le_subgroupOf hT
  have hTYg : T.subgroupOf H ≤ Y.subgroupOf H := fun x hx => hTY hx
  have hPY : ((T.subgroupOf H).map (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H))).map
        (φ : OTwoQuot H →* W3) ≤
      ((Y.subgroupOf H).map (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H))).map
        (φ : OTwoQuot H →* W3) :=
    Subgroup.map_mono (Subgroup.map_mono hTYg)
  rcases W3.sylow_maximal (isSylowTwoOf_image hT φ) hPY with h | h
  · left
    have h1 : (Y.subgroupOf H).map (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H)) =
        (T.subgroupOf H).map (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H)) :=
      Subgroup.map_injective (f := (φ : OTwoQuot H →* W3)) φ.injective h
    have h2 : Y.subgroupOf H = T.subgroupOf H := by
      have := congrArg (Subgroup.comap (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H))) h1
      rwa [Subgroup.comap_map_eq_self (hker.trans hTYg),
        Subgroup.comap_map_eq_self hker] at this
    have h3 : Y ⊓ H = T ⊓ H := Subgroup.subgroupOf_inj.mp h2
    rwa [inf_eq_left.mpr hYH, inf_eq_left.mpr hT.1] at h3
  · right
    have h1 : (Y.subgroupOf H).map (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H)) = ⊤ := by
      refine Subgroup.map_injective (f := (φ : OTwoQuot H →* W3)) φ.injective ?_
      rw [h, Subgroup.map_top_of_surjective _ φ.surjective]
    have h2 : Y.subgroupOf H = ⊤ := by
      have := congrArg (Subgroup.comap (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H))) h1
      rwa [Subgroup.comap_map_eq_self (hker.trans hTYg), Subgroup.comap_top] at this
    exact le_antisymm hYH (Subgroup.subgroupOf_eq_top.mp h2)

end S152N

end CFSG.Quasithin
