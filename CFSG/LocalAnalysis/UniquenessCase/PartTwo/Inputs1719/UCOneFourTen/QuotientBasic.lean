module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.Defs
import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.L3YC.ModO2Iso
import CFSG.GroupTheory.Commutator.SubgroupOf
import CFSG.Goldschmidt.Steps.G36Setup
import CFSG.RankThree.PartOne.S9.Extraction.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UC410

open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isSz_bar2_map {H L : Subgroup G} {n : ℕ} (hLH : L ≤ H) (hSz : IsSz (Bar2 L) n) :
    IsSz (Bar2 ((L.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)))) n := by
  obtain ⟨e⟩ := CFSG.Quasithin.Stellmacher.CD.L3YC.modO2_modO2Image_equiv (H := H) hLH
  exact CFSG.Blueprint.LieModel.of_mulEquiv e.symm hSz

omit [Finite G] in
theorem commutator_map_self {H L : Subgroup G} (hLH : L ≤ H) (hL : ⁅L, L⁆ = L) :
    ⁅(L.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)),
      (L.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H))⁆ =
      (L.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) := by
  rw [← Subgroup.map_commutator, CFSG.GroupTheory.commutator_subgroupOf_eq hLH hLH, hL]

private theorem pRank_le_eM {M : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    CFSG.Open.pRank p M ≤ S17.eM M := by
  unfold CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.eM
  refine le_csSup ⟨Nat.card G, ?_⟩ ⟨p, hp, hp2, rfl⟩
  rintro n ⟨q, hq, hq2, rfl⟩
  exact CFSG.SectionRank.pRank_le_card_of_one_lt hq.one_lt M

theorem pRank_top_quotient_le {H : Subgroup G} (heM : S17.eM H ≤ 3) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) : CFSG.Open.pRank p (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) ≤ 3 := by
  have hq : CFSG.Open.pRank p (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) =
      CFSG.Open.pRank p (⊤ : Subgroup ↥H) :=
    CFSG.SectionRank.pRank_quotient_two_group (G := ↥H) (P := CFSG.pCore 2 ↥H)
      (CFSG.pCore_isPGroup (p := 2) (G := ↥H)) hp hp2
  rw [hq, ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := p) H]
  exact (pRank_le_eM hp hp2).trans heM

theorem eM_le_of_le {H₁ H : Subgroup G} (h : H₁ ≤ H) (heM : S17.eM H ≤ 3) :
    S17.eM H₁ ≤ 3 := by
  unfold CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.eM at *
  refine csSup_le' fun n hn => ?_
  obtain ⟨q, hq, hq2, rfl⟩ := hn
  exact (CFSG.SectionRank.pRank_mono hq.one_lt h).trans ((pRank_le_eM hq hq2).trans heM)

omit [Finite G] in
theorem isSubnormal_map {H L W : Subgroup G} (h : CFSG.Open.IsSubnormal L W) :
    CFSG.Open.IsSubnormal ((L.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)))
      ((W.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H))) := by
  exact CFSG.Open.IsSubnormal.map (QuotientGroup.mk' (CFSG.pCore 2 ↥H))
    (CFSG.Open.IsSubnormal.comap H.subtype h)

omit [Finite G] in
theorem exists_preimage {H : Subgroup G} (X₁ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) :
    ∃ H₁ : Subgroup G, H₁ ≤ H ∧ CFSG.Open.pCoreOf 2 H ≤ H₁ ∧
      (H₁.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) = X₁ := by
  refine ⟨(X₁.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥H))).map H.subtype,
    Subgroup.map_subtype_le _, ?_, ?_⟩
  · rintro x ⟨y, hy, rfl⟩
    refine Subgroup.mem_map_of_mem H.subtype ?_
    rw [Subgroup.mem_comap]
    have hy1 : QuotientGroup.mk' (CFSG.pCore 2 ↥H) y = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hy
    rw [hy1]
    exact X₁.one_mem
  · have hsub : ((X₁.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥H))).map
        H.subtype).subgroupOf H = X₁.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) := by
      ext z
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
      constructor
      · rintro ⟨y, hy, hzy⟩
        rwa [← Subtype.ext hzy]
      · intro hz
        exact ⟨z, hz, rfl⟩
    rw [hsub]
    exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) X₁

theorem pCore_quotient_eq_bot (H : Subgroup G) :
    CFSG.pCore 2 (↥H ⧸ CFSG.pCore 2 ↥H) = ⊥ := by
  exact CFSG.RankThree.PartOne.Extract.pCore_two_quotient_eq_bot (H := ↥H)

omit [Finite G] in
theorem le_of_map_le {H L W : Subgroup G} (hLH : L ≤ H) (hQW : CFSG.Open.pCoreOf 2 H ≤ W)
    (h : (L.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) ≤
      (W.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H))) : L ≤ W := by
  have hker : (QuotientGroup.mk' (CFSG.pCore 2 ↥H)).ker ≤ W.subgroupOf H := by
    intro x hx
    rw [QuotientGroup.ker_mk'] at hx
    exact hQW (Subgroup.mem_map_of_mem H.subtype hx)
  have hcm : Subgroup.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥H))
      (Subgroup.map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) (W.subgroupOf H)) = W.subgroupOf H := by
    rw [Subgroup.comap_map_eq]
    exact sup_eq_left.mpr hker
  have hsub : L.subgroupOf H ≤ W.subgroupOf H := by
    have h1 : L.subgroupOf H ≤ Subgroup.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥H))
        (Subgroup.map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) (W.subgroupOf H)) := by
      intro x hx
      exact h (Subgroup.mem_map_of_mem _ hx)
    rwa [hcm] at h1
  intro x hx
  have hx' : (⟨x, hLH hx⟩ : ↥H) ∈ W.subgroupOf H :=
    hsub (show (⟨x, hLH hx⟩ : ↥H) ∈ L.subgroupOf H from hx)
  exact hx'

omit [Finite G] in
theorem eq_of_map_eq_top {H W : Subgroup G} (hWH : W ≤ H) (hQW : CFSG.Open.pCoreOf 2 H ≤ W)
    (h : (W.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) = ⊤) : W = H := by
  have hHtop : (H.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) = ⊤ := by
    rw [Subgroup.subgroupOf_self, Subgroup.map_top]
    exact MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)
  have hle : H ≤ W :=
    le_of_map_le le_rfl hQW (by rw [hHtop, h])
  exact le_antisymm hWH hle

omit [Finite G] in
theorem isSubnormal_of_map_top {H M L : Subgroup G} (hMH : M ≤ H)
    (hQM : CFSG.Open.pCoreOf 2 H ≤ M) (hL : CFSG.Open.IsSubnormal L M)
    (h : CFSG.Open.IsSubnormal ((L.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H))) ⊤) :
    CFSG.Open.IsSubnormal L H := by
  set φ := QuotientGroup.mk' (CFSG.pCore 2 ↥H) with hφ
  set Y : Subgroup G :=
    Subgroup.map H.subtype (Subgroup.comap φ (Subgroup.map φ (L.subgroupOf H))) with hY
  have hLleM : L ≤ M := CFSG.Open.IsSubnormal.le hL
  have hPM : CFSG.pCore 2 ↥H ≤ M.subgroupOf H := by
    intro x hx
    exact hQM (Subgroup.mem_map_of_mem H.subtype hx)
  have hLsubM : L.subgroupOf H ≤ M.subgroupOf H := Subgroup.subgroupOf_mono H hLleM
  have hcomap_le : Subgroup.comap φ (Subgroup.map φ (L.subgroupOf H)) ≤ M.subgroupOf H := by
    calc Subgroup.comap φ (Subgroup.map φ (L.subgroupOf H))
        = L.subgroupOf H ⊔ φ.ker := Subgroup.comap_map_eq φ (L.subgroupOf H)
      _ = L.subgroupOf H ⊔ CFSG.pCore 2 ↥H := by rw [QuotientGroup.ker_mk']
      _ ≤ M.subgroupOf H := sup_le hLsubM hPM
  have hYleM : Y ≤ M := by
    rw [hY, ← Subgroup.map_subgroupOf_eq_of_le hMH]
    exact Subgroup.map_mono hcomap_le
  have hLY : L ≤ Y := by
    intro x hx
    have hxH : x ∈ H := hMH (hLleM hx)
    rw [hY]
    refine Subgroup.mem_map_of_mem H.subtype
      (show (⟨x, hxH⟩ : ↥H) ∈ Subgroup.comap φ (Subgroup.map φ (L.subgroupOf H)) from ?_)
    rw [Subgroup.mem_comap]
    exact Subgroup.mem_map_of_mem φ (show (⟨x, hxH⟩ : ↥H) ∈ L.subgroupOf H from hx)
  have hLsnY : CFSG.Open.IsSubnormal L Y :=
    CFSG.Goldschmidt.isSubnormal_of_subgroupOf hLY
      (CFSG.GroupTheory.isSubnormal_subgroupOf_of_le hYleM
        (CFSG.Open.IsSubnormal.subgroupOf hL))
  have hYsn : CFSG.Open.IsSubnormal Y H := by
    have h1 : CFSG.Open.IsSubnormal
        (Subgroup.comap φ (Subgroup.map φ (L.subgroupOf H))) ⊤ := by
      simpa using (CFSG.Open.IsSubnormal.comap φ h :
        CFSG.Open.IsSubnormal (Subgroup.comap φ (Subgroup.map φ (L.subgroupOf H)))
          (Subgroup.comap φ ⊤))
    have h2 := CFSG.Open.IsSubnormal.map H.subtype h1
    rw [hY]
    rwa [Subgroup.map_top, Subgroup.range_subtype] at h2
  exact CFSG.Open.IsSubnormal.trans hLsnY hYsn

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UC410
