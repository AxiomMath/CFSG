module

public import CFSG.Quasithin.Background.E2TwoProofBar

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace F146Field

namespace Swap

variable {G : Type} [Group G] {H : Subgroup G}

theorem cjSub_mem_cComp {K : Subgroup G} (hK : K ∈ cComp H) {s : G} (hs : s ∈ H) :
    cjSub s K ∈ cComp H := by
  have h1 := cComp_map_mulEquiv (MulAut.conj s) hK
  have h2 : H.map (MulAut.conj s).toMonoidHom = H :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hs)
  rw [h2] at h1
  exact h1

theorem kbar_mem_cComp_top [Finite G] {K : Subgroup G} (hK : K ∈ cComp H) :
    E2P.kbar H K ∈ cComp (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) :=
  map_mem_cComp_top (E2P.barMap H) (QuotientGroup.mk'_surjective _) (E2P.isSolvable_ker_barMap H)
    (subgroupOf_mem_cComp hK)

theorem kbar_injOn [Finite G] : Set.InjOn (E2P.kbar H) (cComp H) := by
  intro K₁ h₁ K₂ h₂ h
  have hb := cComp_map_bijOn (E2P.barMap H) (QuotientGroup.mk'_surjective _)
    (E2P.isSolvable_ker_barMap H)
  exact (cComp_subgroupOf_bijOn H).injOn h₁ h₂
    (hb.injOn (subgroupOf_mem_cComp h₁) (subgroupOf_mem_cComp h₂) h)

theorem subgroupOf_cjSub (K : Subgroup G) {s : G} (hs : s ∈ H) :
    (cjSub s K).subgroupOf H = cjSub (⟨s, hs⟩ : ↥H) (K.subgroupOf H) := by
  ext x
  rw [Subgroup.mem_subgroupOf, mem_cjSub, mem_cjSub, Subgroup.mem_subgroupOf]
  rfl

theorem kbar_cjSub (K : Subgroup G) {s : G} (hs : s ∈ H) :
    E2P.kbar H (cjSub s K) = cjSub (E2P.barMap H ⟨s, hs⟩) (E2P.kbar H K) := by
  unfold E2P.kbar
  rw [subgroupOf_cjSub K hs]
  unfold cjSub
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem isSylowTwoOf_bar {T : Subgroup G} (hT : IsSylowTwoOf T H) :
    IsSylowTwoOf ((T.subgroupOf H).map (E2P.barMap H)) ⊤ := by
  have hS2 : IsPGroup 2 (T.subgroupOf H) :=
    hT.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hT.1).symm
  refine ⟨le_top, hS2.map _, ?_⟩
  have h : (((T.subgroupOf H).map (E2P.barMap H)).subgroupOf ⊤).index =
      ((T.subgroupOf H).map (E2P.barMap H)).index := Subgroup.relIndex_top_right _
  rw [h]
  exact fun hd => hT.2.2 (hd.trans (Subgroup.index_map_dvd _ (QuotientGroup.mk'_surjective _)))

end Swap

end F146Field

end CFSG.Quasithin
