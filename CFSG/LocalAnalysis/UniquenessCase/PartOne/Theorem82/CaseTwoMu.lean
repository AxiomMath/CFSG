module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoP1Defs
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs
import all CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoSylow
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoShapeB
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoO2Ky
import CFSG.GroupTheory.SteinbergCBFTFactorization
import CFSG.Quasithin.Background.B1ChiefCount

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace CaseTwoTransitive

variable {c : Ctx812E G} (t : CaseTwoTransitive c)

private theorem uniqueTwoLocal_sup_of_isMuStar {Y : Subgroup G} (hY : t.IsMuStar Y)
    {W : Subgroup G} (hWM : W ≤ c.S.M) (hW2 : IsPGroup 2 W)
    (hYW : Y ≤ Subgroup.normalizer (W : Set G))
    (hW : ¬ W ≤ CFSG.Open.pCoreOf 2 Y) :
    UniqueTwoLocal c.S.M (Y ⊔ W) := by
  classical
  have hYM : Y ≤ c.S.M := hY.1.1
  have hYeq : Y = t.Ky ⊔ CFSG.Open.pCoreOf 2 Y := hY.1.2.1
  have hR2 : IsPGroup 2 (CFSG.Open.pCoreOf 2 Y) :=
    CFSG.PreuniquenessRankFour.Helpers.pCoreOf_isPGroup 2 Y
  have hRY : CFSG.Open.pCoreOf 2 Y ≤ Y :=
    CFSG.PreuniquenessRankFour.Helpers.pCoreOf_le 2 Y
  have hYR : Y ≤ Subgroup.normalizer ((CFSG.Open.pCoreOf 2 Y) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRY).mp
      (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_normal 2 Y)
  have hYH : Y ≤ Y ⊔ W := le_sup_left
  have hWH : W ≤ Y ⊔ W := le_sup_right
  have hWH_norm : Y ⊔ W ≤ Subgroup.normalizer (W : Set G) :=
    sup_le hYW Subgroup.le_normalizer
  have hWn : (W.subgroupOf (Y ⊔ W)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).mpr hWH_norm
  have hWT : W ≤ CFSG.Open.pCoreOf 2 (Y ⊔ W) :=
    CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 W (Y ⊔ W) hWH hWn hW2
  have hTH : CFSG.Open.pCoreOf 2 (Y ⊔ W) ≤ Y ⊔ W :=
    CFSG.PreuniquenessRankFour.Helpers.pCoreOf_le 2 (Y ⊔ W)
  have hT2 : IsPGroup 2 (CFSG.Open.pCoreOf 2 (Y ⊔ W)) :=
    CFSG.PreuniquenessRankFour.Helpers.pCoreOf_isPGroup 2 (Y ⊔ W)
  have hTnorm : (CFSG.Open.pCoreOf 2 (Y ⊔ W)).subgroupOf (Y ⊔ W) |>.Normal :=
    CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_normal 2 (Y ⊔ W)
  have hHN_T : Y ⊔ W ≤
      Subgroup.normalizer ((CFSG.Open.pCoreOf 2 (Y ⊔ W)) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hTH).mp hTnorm
  have hRH : CFSG.Open.pCoreOf 2 Y ≤ Y ⊔ W := hRY.trans hYH
  have hR_NT : CFSG.Open.pCoreOf 2 Y ≤
      Subgroup.normalizer ((CFSG.Open.pCoreOf 2 (Y ⊔ W)) : Set G) :=
    hRH.trans hHN_T
  have hRT2 : IsPGroup 2
      ((CFSG.Open.pCoreOf 2 Y ⊔ CFSG.Open.pCoreOf 2 (Y ⊔ W) : Subgroup G)) :=
    IsPGroup.to_sup_of_normal_right' hR2 hT2 hR_NT
  have hY_NRT : Y ≤ Subgroup.normalizer
      ((CFSG.Open.pCoreOf 2 Y ⊔ CFSG.Open.pCoreOf 2 (Y ⊔ W) : Subgroup G) : Set G) := by
    intro y hy
    exact Subgroup.inf_normalizer_le_normalizer_sup _ _
      ⟨hYR hy, hYH.trans hHN_T hy⟩
  have hT_NRT : CFSG.Open.pCoreOf 2 (Y ⊔ W) ≤ Subgroup.normalizer
      ((CFSG.Open.pCoreOf 2 Y ⊔ CFSG.Open.pCoreOf 2 (Y ⊔ W) : Subgroup G) : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro x hxT y hy
    have hmap : ((CFSG.Open.pCoreOf 2 Y ⊔ CFSG.Open.pCoreOf 2 (Y ⊔ W)).map
        (MulAut.conj x).toMonoidHom) ≤
        (CFSG.Open.pCoreOf 2 Y ⊔ CFSG.Open.pCoreOf 2 (Y ⊔ W)) := by
      rw [Subgroup.map_sup]
      refine sup_le ?_ ?_
      · rintro - ⟨r, hrR, rfl⟩
        have hconj : r * x * r⁻¹ ∈ CFSG.Open.pCoreOf 2 (Y ⊔ W) := by
          have h := hTnorm.conj_mem ⟨x, hTH hxT⟩ (Subgroup.mem_subgroupOf.mpr hxT)
            ⟨r, hRH hrR⟩
          simpa [Subgroup.mem_subgroupOf] using h
        have hxrx : (MulEquiv.toMonoidHom (MulAut.conj x)) r = x * r * x⁻¹ := by
          simp [MulAut.conj_apply]
        rw [hxrx]
        have heq : x * r * x⁻¹ = (x * (r * x * r⁻¹)⁻¹) * r := by group
        rw [heq]
        exact (CFSG.Open.pCoreOf 2 Y ⊔ CFSG.Open.pCoreOf 2 (Y ⊔ W)).mul_mem
          (Subgroup.mem_sup_right
            ((CFSG.Open.pCoreOf 2 (Y ⊔ W)).mul_mem hxT
              ((CFSG.Open.pCoreOf 2 (Y ⊔ W)).inv_mem hconj)))
          (Subgroup.mem_sup_left hrR)
      · rintro - ⟨s, hsT, rfl⟩
        have hxsx : (MulEquiv.toMonoidHom (MulAut.conj x)) s = x * s * x⁻¹ := by
          simp [MulAut.conj_apply]
        rw [hxsx]
        exact Subgroup.mem_sup_right
          ((CFSG.Open.pCoreOf 2 (Y ⊔ W)).mul_mem
            ((CFSG.Open.pCoreOf 2 (Y ⊔ W)).mul_mem hxT hsT)
            ((CFSG.Open.pCoreOf 2 (Y ⊔ W)).inv_mem hxT))
    exact hmap ⟨y, hy, rfl⟩
  have hH_NRT : Y ⊔ W ≤ Subgroup.normalizer
      ((CFSG.Open.pCoreOf 2 Y ⊔ CFSG.Open.pCoreOf 2 (Y ⊔ W) : Subgroup G) : Set G) :=
    sup_le hY_NRT (hWT.trans hT_NRT)
  have hRT_le : CFSG.Open.pCoreOf 2 Y ⊔ CFSG.Open.pCoreOf 2 (Y ⊔ W) ≤
      CFSG.Open.pCoreOf 2 (Y ⊔ W) := by
    refine CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 _ (Y ⊔ W)
      (sup_le hRH hTH) ?_ hRT2
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer (sup_le hRH hTH)).mpr hH_NRT
  have hR_le_T : CFSG.Open.pCoreOf 2 Y ≤ CFSG.Open.pCoreOf 2 (Y ⊔ W) :=
    le_sup_left.trans hRT_le
  have hT1 : CFSG.Open.pCoreOf 2 (Y ⊔ W) ≠ ⊥ := by
    intro hbot
    have hW1 : W = ⊥ := le_bot_iff.mp (hWT.trans (le_of_eq hbot))
    exact hW (by rw [hW1]; exact bot_le)
  have hH_eq : Y ⊔ W = t.Ky ⊔ CFSG.Open.pCoreOf 2 (Y ⊔ W) := by
    apply le_antisymm
    · refine sup_le ?_ ?_
      · nth_rewrite 1 [hYeq]
        exact sup_le le_sup_left (hR_le_T.trans le_sup_right)
      · exact hWT.trans le_sup_right
    · refine sup_le ?_ hTH
      have hKY' : t.Ky ≤ Y := by
        rw [hYeq]
        exact le_sup_left
      exact hKY'.trans le_sup_left
  by_contra hnot
  have hHmu : t.IsMu (Y ⊔ W) := ⟨sup_le hYM hWM, hH_eq, hT1, hnot⟩
  have heq : Y ⊔ W = Y := hY.2 (Y ⊔ W) hHmu le_sup_left
  have hWY : W ≤ Y := heq ▸ le_sup_right
  have hWnY : (W.subgroupOf Y).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hWY).mpr hYW
  have hWR : W ≤ CFSG.Open.pCoreOf 2 Y :=
    CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 W Y hWY hWnY hW2
  exact hW hWR

theorem exists_isMuStar (hne : ¬ UniqueTwoLocal c.S.M t.Ky) : ∃ Y : Subgroup G, t.IsMuStar Y := by
  classical
  have hMN : c.S.M ≤ Subgroup.normalizer (t.d.N : Set G) := by
    rw [← t.hdM]
    exact SylowThreeData.N_normal t.d
  have hO2 : CFSG.Open.pCoreOf 2 t.Ky ≠ ⊥ := by
    intro hbot
    have hA_norm : ((t.Ky ⊓ t.d.N).subgroupOf t.Ky).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left]
      intro x hx
      exact Subgroup.inf_normalizer_le_normalizer_inf
        ⟨Subgroup.le_normalizer hx, hMN ((t.Ky_le.trans inf_le_left).trans
          c.hyp81.1 hx)⟩
    have hA2 : IsPGroup 2 ((t.Ky ⊓ t.d.N : Subgroup G)) :=
      (SylowThreeData.N_isPGroup t.d).to_le inf_le_right
    have hA_le : t.Ky ⊓ t.d.N ≤ CFSG.Open.pCoreOf 2 t.Ky :=
      CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 _ _ inf_le_left
        hA_norm hA2
    have hA_bot : t.Ky ⊓ t.d.N = ⊥ := le_bot_iff.mp (by simpa [hbot] using hA_le)
    have hcomm_le : ⁅t.Ky ⊓ t.d.N, t.Z⁆ ≤ t.Ky ⊓ t.d.N := by
      rw [Subgroup.commutator_le]
      intro a ha z hz
      have hzKy : z ∈ t.Ky := t.Z_le_Ky hz
      have hzM : z ∈ c.S.M := (t.Ky_le.trans inf_le_left).trans c.hyp81.1 hzKy
      have hconj : z * a * z⁻¹ ∈ t.Ky ⊓ t.d.N := by
        refine ⟨?_, ?_⟩
        · exact t.Ky.mul_mem (t.Ky.mul_mem hzKy ha.1) (t.Ky.inv_mem hzKy)
        · exact (Subgroup.mem_normalizer_iff.mp (hMN hzM) a).mp ha.2
      have hcomm : ⁅a, z⁆ = a * (z * a * z⁻¹)⁻¹ := by
        rw [commutatorElement_def]
        group
      rw [hcomm]
      exact (t.Ky ⊓ t.d.N).mul_mem ha ((t.Ky ⊓ t.d.N).inv_mem hconj)
    exact t.commutator_Ky_inf_N_Z_ne_bot
      (le_bot_iff.mp (hcomm_le.trans (le_of_eq hA_bot)))
  have hKyMu : t.IsMu t.Ky := by
    refine ⟨(t.Ky_le.trans inf_le_left).trans c.hyp81.1, ?_, hO2, hne⟩
    exact (sup_eq_left.mpr (CFSG.PreuniquenessRankFour.Helpers.pCoreOf_le 2 t.Ky)).symm
  obtain ⟨Y, hKY, hmax⟩ :=
    (Set.toFinite {Y : Subgroup G | t.IsMu Y}).exists_le_maximal hKyMu
  exact ⟨Y, hmax.prop, fun Y' hY' hle => (hmax.eq_of_le hY' hle).symm⟩

theorem normalizer_le_of_le_pCoreOf (hη : t.KyInEta) {Y : Subgroup G} (hY : t.IsMuStar Y)
    {C : Subgroup G} (hCR : C ≤ CFSG.Open.pCoreOf 2 Y) (hC1 : C ≠ ⊥)
    (hCc : (C.subgroupOf (CFSG.Open.pCoreOf 2 Y)).Characteristic) :
    Subgroup.normalizer (C : Set G) ≤ c.S.M := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hR2 : IsPGroup 2 (CFSG.Open.pCoreOf 2 Y) :=
    CFSG.PreuniquenessRankFour.Helpers.pCoreOf_isPGroup 2 Y
  have hRM : CFSG.Open.pCoreOf 2 Y ≤ c.S.M :=
    (CFSG.PreuniquenessRankFour.Helpers.pCoreOf_le 2 Y).trans hY.1.1
  have hC2 : IsPGroup 2 C := hR2.to_le hCR
  have hloc : CFSG.Open.IsTwoLocal (Subgroup.normalizer (C : Set G)) :=
    ⟨C, hC1, hC2, rfl⟩
  have hRC : Subgroup.normalizer ((CFSG.Open.pCoreOf 2 Y) : Set G) ≤
      Subgroup.normalizer (C : Set G) := by
    have h := CFSG.PreuniquenessRankFour.Helpers.normalizer_le_normalizer_characteristic
      (C.subgroupOf (CFSG.Open.pCoreOf 2 Y)) hCc
    rwa [Subgroup.map_subgroupOf_eq_of_le hCR] at h
  have hKY : t.Ky ≤ Y := by
    rw [hY.1.2.1]
    exact le_sup_left
  have hKYR : t.Ky ≤ Subgroup.normalizer ((CFSG.Open.pCoreOf 2 Y) : Set G) :=
    hKY.trans (CFSG.PreuniquenessRankFour.Helpers.subgroup_normalizes_pCoreOf 2 Y)
  by_cases hQR : c.L ⊓ t.d.N ≤ CFSG.Open.pCoreOf 2 Y
  · have hηR := hη (CFSG.Open.pCoreOf 2 Y) hRM hR2 hKYR hQR
    exact hηR _ hloc (inf_le_right.trans hRC)
  · have hQ2 : IsPGroup 2 ((c.L ⊓ t.d.N : Subgroup G)) := t.inf_N_isPGroup
    have hQnorm : c.S.M ≤
        Subgroup.normalizer ((c.L ⊓ t.d.N : Subgroup G) : Set G) := t.le_normalizer_inf_N
    have hS2 : IsPGroup 2
        ((CFSG.Open.pCoreOf 2 Y ⊔ (c.L ⊓ t.d.N) : Subgroup G)) :=
      IsPGroup.to_sup_of_normal_right' hR2 hQ2 (hRM.trans hQnorm)
    have hRS : CFSG.Open.pCoreOf 2 Y <
        (CFSG.Open.pCoreOf 2 Y ⊔ (c.L ⊓ t.d.N : Subgroup G)) :=
      lt_of_le_of_ne le_sup_left fun hEq => hQR (hEq ▸ le_sup_right)
    have hlt := CFSG.GroupTheory.FT63ChII.lt_inf_normalizer_of_lt hS2 hRS
    have hWM : ((CFSG.Open.pCoreOf 2 Y ⊔ (c.L ⊓ t.d.N : Subgroup G)) ⊓
        Subgroup.normalizer ((CFSG.Open.pCoreOf 2 Y) : Set G)) ≤ c.S.M :=
      inf_le_left.trans (sup_le hRM (t.inf_N_le_M))
    have hW2 : IsPGroup 2 ((((CFSG.Open.pCoreOf 2 Y ⊔ (c.L ⊓ t.d.N) : Subgroup G)) ⊓
        Subgroup.normalizer ((CFSG.Open.pCoreOf 2 Y) : Set G) : Subgroup G)) :=
      hS2.to_le inf_le_left
    have hYW : Y ≤ Subgroup.normalizer
        (((CFSG.Open.pCoreOf 2 Y ⊔ (c.L ⊓ t.d.N : Subgroup G)) ⊓
          Subgroup.normalizer ((CFSG.Open.pCoreOf 2 Y) : Set G) : Subgroup G) : Set G) := by
      intro y hy
      refine Subgroup.inf_normalizer_le_normalizer_inf ⟨?_, ?_⟩
      · exact Subgroup.inf_normalizer_le_normalizer_sup _ _
          ⟨(CFSG.PreuniquenessRankFour.Helpers.subgroup_normalizes_pCoreOf 2 Y) hy,
            (hY.1.1.trans hQnorm) hy⟩
      · exact Subgroup.le_normalizer
          ((CFSG.PreuniquenessRankFour.Helpers.subgroup_normalizes_pCoreOf 2 Y) hy)
    have hUnique := t.uniqueTwoLocal_sup_of_isMuStar hY hWM hW2 hYW hlt.2
    refine hUnique _ hloc (sup_le ?_ ?_)
    · exact (CFSG.PreuniquenessRankFour.Helpers.subgroup_normalizes_pCoreOf 2 Y).trans hRC
    · exact inf_le_right.trans hRC

theorem le_pCoreOf_of_isCalH (hη : t.KyInEta) {Y : Subgroup G} (hY : t.IsMuStar Y)
    {H : Subgroup G} (hH : IsCalH c.S.M Y H) {T : Subgroup G} (hT : IsPGroup 2 T) (hTH : T ≤ H)
    (hYT : Y ≤ Subgroup.normalizer (T : Set G)) : T ≤ CFSG.Open.pCoreOf 2 Y := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hYR : Y ≤ Subgroup.normalizer ((CFSG.Open.pCoreOf 2 Y) : Set G) :=
    CFSG.PreuniquenessRankFour.Helpers.subgroup_normalizes_pCoreOf 2 Y
  have hNS : Subgroup.normalizer ((CFSG.Open.pCoreOf 2 Y) : Set G) ≤ c.S.M :=
    t.normalizer_le_of_le_pCoreOf hη hY le_rfl hY.1.2.2.1
      (by rw [Subgroup.subgroupOf_self]; infer_instance)
  have hkey : ∀ S : Subgroup G, IsPGroup 2 S → S ≤ H → Y ≤ Subgroup.normalizer (S : Set G) →
      CFSG.Open.pCoreOf 2 Y ≤ S → S ≤ CFSG.Open.pCoreOf 2 Y := by
    intro S hS2 hSH hYS hRS
    by_contra hSR
    have hlt : CFSG.Open.pCoreOf 2 Y < S :=
      lt_of_le_of_ne hRS (fun h => hSR (le_of_eq h.symm))
    have hW2 : IsPGroup 2
        ((S ⊓ Subgroup.normalizer ((CFSG.Open.pCoreOf 2 Y) : Set G) : Subgroup G)) :=
      hS2.to_le inf_le_left
    have hWM : S ⊓ Subgroup.normalizer ((CFSG.Open.pCoreOf 2 Y) : Set G) ≤ c.S.M :=
      inf_le_right.trans hNS
    have hYW : Y ≤ Subgroup.normalizer
        ((S ⊓ Subgroup.normalizer ((CFSG.Open.pCoreOf 2 Y) : Set G) : Subgroup G) : Set G) := by
      intro y hy
      exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hYS hy, Subgroup.le_normalizer (hYR hy)⟩
    have hltW := CFSG.GroupTheory.FT63ChII.lt_inf_normalizer_of_lt hS2 hlt
    have hUnique := t.uniqueTwoLocal_sup_of_isMuStar hY hWM hW2 hYW hltW.2
    have hO2 : IsPGroup 2 (CFSG.Open.pCoreOf 2 H) :=
      CFSG.PreuniquenessRankFour.Helpers.pCoreOf_isPGroup 2 H
    have hHN : H ≤ Subgroup.normalizer ((CFSG.Open.pCoreOf 2 H) : Set G) :=
      CFSG.PreuniquenessRankFour.Helpers.subgroup_normalizes_pCoreOf 2 H
    have hloc : CFSG.Open.IsTwoLocal
        (Subgroup.normalizer ((CFSG.Open.pCoreOf 2 H) : Set G)) :=
      ⟨CFSG.Open.pCoreOf 2 H, hH.2.2, hO2, rfl⟩
    have hcont : Y ⊔ (S ⊓ Subgroup.normalizer ((CFSG.Open.pCoreOf 2 Y) : Set G)) ≤
        Subgroup.normalizer ((CFSG.Open.pCoreOf 2 H) : Set G) :=
      sup_le (hH.1.trans hHN) ((inf_le_left.trans hSH).trans hHN)
    have hNM := hUnique _ hloc hcont
    exact hH.2.1 (hHN.trans hNM)
  have hTsup2 : IsPGroup 2 ((T ⊔ CFSG.Open.pCoreOf 2 Y : Subgroup G)) :=
    IsPGroup.to_sup_of_normal_left' hT (CFSG.PreuniquenessRankFour.Helpers.pCoreOf_isPGroup 2 Y)
      ((CFSG.PreuniquenessRankFour.Helpers.pCoreOf_le 2 Y).trans hYT)
  have hTsupH : T ⊔ CFSG.Open.pCoreOf 2 Y ≤ H :=
    sup_le hTH ((CFSG.PreuniquenessRankFour.Helpers.pCoreOf_le 2 Y).trans hH.1)
  have hYTsup : Y ≤ Subgroup.normalizer ((T ⊔ CFSG.Open.pCoreOf 2 Y : Subgroup G) : Set G) := by
    intro y hy
    exact Subgroup.inf_normalizer_le_normalizer_sup _ _ ⟨hYT hy, hYR hy⟩
  exact le_sup_left.trans (hkey _ hTsup2 hTsupH hYTsup le_sup_right)

theorem charTwo_of_isCalH (hη : t.KyInEta) {Y : Subgroup G} (hY : t.IsMuStar Y)
    {H : Subgroup G} (hH : IsCalH c.S.M Y H) : CFSG.QuasithinUnique.CharTwo H := by
  classical
  have hO2 : IsPGroup 2 (CFSG.Open.pCoreOf 2 H) :=
    CFSG.PreuniquenessRankFour.Helpers.pCoreOf_isPGroup 2 H
  have hO2le : CFSG.Open.pCoreOf 2 H ≤ H :=
    CFSG.PreuniquenessRankFour.Helpers.pCoreOf_le 2 H
  have hHN : H ≤ Subgroup.normalizer ((CFSG.Open.pCoreOf 2 H) : Set G) :=
    CFSG.PreuniquenessRankFour.Helpers.subgroup_normalizes_pCoreOf 2 H
  have hloc : CFSG.Open.IsTwoLocal
      (Subgroup.normalizer ((CFSG.Open.pCoreOf 2 H) : Set G)) :=
    ⟨CFSG.Open.pCoreOf 2 H, hH.2.2, hO2, rfl⟩
  have hnotM : ¬ Subgroup.normalizer ((CFSG.Open.pCoreOf 2 H) : Set G) ≤ c.S.M :=
    fun hle => hH.2.1 (hHN.trans hle)
  have hO2N : IsPGroup 2
      (CFSG.Open.pCoreOf 2 (Subgroup.normalizer ((CFSG.Open.pCoreOf 2 H) : Set G))) :=
    CFSG.PreuniquenessRankFour.Helpers.pCoreOf_isPGroup 2 _
  have hleN : CFSG.Open.pCoreOf 2 H ≤
      CFSG.Open.pCoreOf 2 (Subgroup.normalizer ((CFSG.Open.pCoreOf 2 H) : Set G)) := by
    refine CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 _ _
      (hO2le.trans hHN) ?_ hO2
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer (hO2le.trans hHN)).mpr le_rfl
  have hNne : CFSG.Open.pCoreOf 2
      (Subgroup.normalizer ((CFSG.Open.pCoreOf 2 H) : Set G)) ≠ ⊥ := by
    intro hbot
    exact hH.2.2 (le_bot_iff.mp (hleN.trans (le_of_eq hbot)))
  have hcalH : IsCalH c.S.M Y
      (Subgroup.normalizer ((CFSG.Open.pCoreOf 2 H) : Set G)) :=
    ⟨hH.1.trans hHN, hnotM, hNne⟩
  have hleR : CFSG.Open.pCoreOf 2
      (Subgroup.normalizer ((CFSG.Open.pCoreOf 2 H) : Set G)) ≤
      CFSG.Open.pCoreOf 2 Y :=
    t.le_pCoreOf_of_isCalH hη hY hcalH hO2N
      (CFSG.PreuniquenessRankFour.Helpers.pCoreOf_le 2 _)
      ((hH.1.trans hHN).trans (CFSG.PreuniquenessRankFour.Helpers.subgroup_normalizes_pCoreOf 2 _))
  have hleH : CFSG.Open.pCoreOf 2
      (Subgroup.normalizer ((CFSG.Open.pCoreOf 2 H) : Set G)) ≤ H :=
    hleR.trans ((CFSG.PreuniquenessRankFour.Helpers.pCoreOf_le 2 Y).trans hH.1)
  have hleO2H : CFSG.Open.pCoreOf 2
      (Subgroup.normalizer ((CFSG.Open.pCoreOf 2 H) : Set G)) ≤
      CFSG.Open.pCoreOf 2 H := by
    refine CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 _ H hleH ?_ hO2N
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hleH).mpr
      (hHN.trans (CFSG.PreuniquenessRankFour.Helpers.subgroup_normalizes_pCoreOf 2 _))
  have hEq : CFSG.Open.pCoreOf 2
      (Subgroup.normalizer ((CFSG.Open.pCoreOf 2 H) : Set G)) = CFSG.Open.pCoreOf 2 H :=
    le_antisymm hleO2H hleN
  have hchar := c.standing.charTwo
    (Subgroup.normalizer ((CFSG.Open.pCoreOf 2 H) : Set G)) hloc
  rw [hEq] at hchar
  intro x hx
  exact hchar ⟨hHN hx.1, hx.2⟩

theorem pCoreOf_le_of_isCalH (hη : t.KyInEta) {Y : Subgroup G} (hY : t.IsMuStar Y)
    {H : Subgroup G} (hH : IsCalH c.S.M Y H) :
    CFSG.Open.pCoreOf 2 H ≤ CFSG.Open.pCoreOf 2 (H ⊓ c.S.M) := by
  classical
  have hO2 : IsPGroup 2 (CFSG.Open.pCoreOf 2 H) :=
    CFSG.PreuniquenessRankFour.Helpers.pCoreOf_isPGroup 2 H
  have hO2H : CFSG.Open.pCoreOf 2 H ≤ H :=
    CFSG.PreuniquenessRankFour.Helpers.pCoreOf_le 2 H
  have hleR : CFSG.Open.pCoreOf 2 H ≤ CFSG.Open.pCoreOf 2 Y :=
    t.le_pCoreOf_of_isCalH hη hY hH hO2 hO2H
      (hH.1.trans (CFSG.PreuniquenessRankFour.Helpers.subgroup_normalizes_pCoreOf 2 H))
  have hleM : CFSG.Open.pCoreOf 2 H ≤ c.S.M :=
    hleR.trans ((CFSG.PreuniquenessRankFour.Helpers.pCoreOf_le 2 Y).trans hY.1.1)
  have hleHM : CFSG.Open.pCoreOf 2 H ≤ H ⊓ c.S.M := le_inf hO2H hleM
  refine CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 _ (H ⊓ c.S.M)
    hleHM ?_ hO2
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hleHM).mpr
    (inf_le_left.trans
      (CFSG.PreuniquenessRankFour.Helpers.subgroup_normalizes_pCoreOf 2 H))

theorem normalizer_le_of_le_of_isCalH (hη : t.KyInEta) {Y : Subgroup G} (hY : t.IsMuStar Y)
    {H : Subgroup G} (hH : IsCalH c.S.M Y H) {P : Subgroup G}
    (hP1 : CFSG.Open.pCoreOf 2 (H ⊓ c.S.M) ≤ P) (hP2 : P ≤ CFSG.Open.pCoreOf 2 Y)
    (hYP : Y ≤ Subgroup.normalizer (P : Set G)) {C : Subgroup G} (hCP : C ≤ P) (hC1 : C ≠ ⊥)
    (hCc : (C.subgroupOf P).Characteristic) : Subgroup.normalizer (C : Set G) ≤ c.S.M := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hR2 : IsPGroup 2 (CFSG.Open.pCoreOf 2 Y) :=
    CFSG.PreuniquenessRankFour.Helpers.pCoreOf_isPGroup 2 Y
  have hRM : CFSG.Open.pCoreOf 2 Y ≤ c.S.M :=
    (CFSG.PreuniquenessRankFour.Helpers.pCoreOf_le 2 Y).trans hY.1.1
  have hP2' : IsPGroup 2 P := hR2.to_le hP2
  have hPM : P ≤ c.S.M := hP2.trans hRM
  have hPC : Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (C : Set G) := by
    have h := CFSG.PreuniquenessRankFour.Helpers.normalizer_le_normalizer_characteristic
      (C.subgroupOf P) hCc
    rwa [Subgroup.map_subgroupOf_eq_of_le hCP] at h
  have hloc : CFSG.Open.IsTwoLocal (Subgroup.normalizer (C : Set G)) :=
    ⟨C, hC1, hP2'.to_le hCP, rfl⟩
  have hKY : t.Ky ≤ Y := by
    rw [hY.1.2.1]
    exact le_sup_left
  by_cases hQP : c.L ⊓ t.d.N ≤ P
  · have hηP := hη P hPM hP2' (hKY.trans hYP) hQP
    exact hηP _ hloc (inf_le_right.trans hPC)
  · have hQ2 : IsPGroup 2 ((c.L ⊓ t.d.N : Subgroup G)) := t.inf_N_isPGroup
    have hQnorm : c.S.M ≤
        Subgroup.normalizer ((c.L ⊓ t.d.N : Subgroup G) : Set G) := t.le_normalizer_inf_N
    have hQn : ((c.L ⊓ t.d.N).subgroupOf c.S.M).Normal := t.inf_N_normal
    have hQHM : (c.L ⊓ t.d.N) ⊓ (H ⊓ c.S.M) ≤ CFSG.Open.pCoreOf 2 (H ⊓ c.S.M) := by
      refine CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 _ (H ⊓ c.S.M)
        inf_le_right ?_ (hQ2.to_le inf_le_left)
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right]
      rw [Subgroup.le_normalizer_iff]
      intro x hx y hy
      refine ⟨?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.mp (t.le_normalizer_inf_N hx.2) y).mp hy.1
      · exact (H ⊓ c.S.M).mul_mem ((H ⊓ c.S.M).mul_mem hx hy.2) ((H ⊓ c.S.M).inv_mem hx)
    have hQY_le : c.L ⊓ t.d.N ⊓ Y ≤ P := by
      refine (le_trans ?_ hQHM).trans hP1
      exact le_inf inf_le_left
        (le_inf (inf_le_right.trans hH.1) (inf_le_left.trans (t.inf_N_le_M)))
    have hPQ2 : IsPGroup 2 ((P ⊔ (c.L ⊓ t.d.N) : Subgroup G)) :=
      IsPGroup.to_sup_of_normal_right' hP2' hQ2 (hPM.trans hQnorm)
    have hlt : P < P ⊔ (c.L ⊓ t.d.N) :=
      lt_of_le_of_ne le_sup_left fun hEq => hQP (hEq ▸ le_sup_right)
    have hltW := CFSG.GroupTheory.FT63ChII.lt_inf_normalizer_of_lt hPQ2 hlt
    have hded : Subgroup.normalizer (P : Set G) ⊓ (P ⊔ (c.L ⊓ t.d.N)) ≤
        P ⊔ (Subgroup.normalizer (P : Set G) ⊓ (c.L ⊓ t.d.N)) :=
      CFSG.Quasithin.ChiefCount.inf_sup_le (H := P)
        (K := Subgroup.normalizer (P : Set G)) (J := c.L ⊓ t.d.N)
        Subgroup.le_normalizer (hPM.trans hQnorm)
    have hWnotP : ¬ ((c.L ⊓ t.d.N) ⊓ Subgroup.normalizer (P : Set G)) ≤ P := by
      intro hle
      have hZle : (P ⊔ (c.L ⊓ t.d.N)) ⊓ Subgroup.normalizer (P : Set G) ≤ P := by
        rw [inf_comm]
        exact hded.trans (le_of_eq (sup_eq_left.mpr (by rwa [inf_comm] at hle)))
      exact hltW.2 hZle
    have hWnotY : ¬ ((c.L ⊓ t.d.N) ⊓ Subgroup.normalizer (P : Set G)) ≤ Y :=
      fun hle => hWnotP ((le_inf inf_le_left hle).trans hQY_le)
    have hWnotR : ¬ ((c.L ⊓ t.d.N) ⊓ Subgroup.normalizer (P : Set G)) ≤
        CFSG.Open.pCoreOf 2 Y :=
      fun hle => hWnotY (hle.trans (CFSG.PreuniquenessRankFour.Helpers.pCoreOf_le 2 Y))
    have hWM : ((c.L ⊓ t.d.N) ⊓ Subgroup.normalizer (P : Set G)) ≤ c.S.M :=
      inf_le_left.trans (t.inf_N_le_M)
    have hW2 : IsPGroup 2 (((c.L ⊓ t.d.N) ⊓ Subgroup.normalizer (P : Set G) : Subgroup G)) :=
      hQ2.to_le inf_le_left
    have hYW : Y ≤ Subgroup.normalizer
        (((c.L ⊓ t.d.N) ⊓ Subgroup.normalizer (P : Set G) : Subgroup G) : Set G) := by
      intro y hy
      exact Subgroup.inf_normalizer_le_normalizer_inf
        ⟨(hY.1.1.trans hQnorm) hy, Subgroup.le_normalizer (hYP hy)⟩
    have hUnique := t.uniqueTwoLocal_sup_of_isMuStar hY hWM hW2 hYW hWnotR
    exact hUnique _ hloc (sup_le (hYP.trans hPC) (inf_le_right.trans hPC))

theorem asc81bHyp_of_isCalH (hη : t.KyInEta) {Y : Subgroup G} (hY : t.IsMuStar Y)
    {H : Subgroup G} (hH : IsCalH c.S.M Y H) :
    CFSG.AGLEmbedding.Asc81bHyp H (CFSG.Open.pCoreOf 2 (H ⊓ c.S.M)) := by
  classical
  have hS2 : IsPGroup 2 (CFSG.Open.pCoreOf 2 (H ⊓ c.S.M)) :=
    CFSG.PreuniquenessRankFour.Helpers.pCoreOf_isPGroup 2 _
  have hSH : CFSG.Open.pCoreOf 2 (H ⊓ c.S.M) ≤ H :=
    (CFSG.PreuniquenessRankFour.Helpers.pCoreOf_le 2 _).trans inf_le_left
  have hO2H : CFSG.Open.pCoreOf 2 H ≤ CFSG.Open.pCoreOf 2 (H ⊓ c.S.M) :=
    t.pCoreOf_le_of_isCalH hη hY hH
  have hS1 : CFSG.Open.pCoreOf 2 (H ⊓ c.S.M) ≠ ⊥ := by
    intro hbot
    exact hH.2.2 (le_bot_iff.mp (hO2H.trans (le_of_eq hbot)))
  have hYS : Y ≤ Subgroup.normalizer ((CFSG.Open.pCoreOf 2 (H ⊓ c.S.M)) : Set G) :=
    (le_inf hH.1 hY.1.1).trans
      (CFSG.PreuniquenessRankFour.Helpers.subgroup_normalizes_pCoreOf 2 (H ⊓ c.S.M))
  have hSR : CFSG.Open.pCoreOf 2 (H ⊓ c.S.M) ≤ CFSG.Open.pCoreOf 2 Y :=
    t.le_pCoreOf_of_isCalH hη hY hH hS2 hSH hYS
  have hSC : ∀ C : Subgroup G, C ≤ CFSG.Open.pCoreOf 2 (H ⊓ c.S.M) → C ≠ ⊥ →
      (C.subgroupOf (CFSG.Open.pCoreOf 2 (H ⊓ c.S.M))).Characteristic →
      Subgroup.normalizer (C : Set G) ≤ c.S.M :=
    fun C hC hC1 hCc =>
      t.normalizer_le_of_le_of_isCalH hη hY hH le_rfl hSR hYS hC hC1 hCc
  have hNS : Subgroup.normalizer ((CFSG.Open.pCoreOf 2 (H ⊓ c.S.M)) : Set G) ≤ c.S.M :=
    hSC _ le_rfl hS1 (by rw [Subgroup.subgroupOf_self]; infer_instance)
  have hHM_N : H ⊓ c.S.M ≤
      Subgroup.normalizer ((CFSG.Open.pCoreOf 2 (H ⊓ c.S.M)) : Set G) :=
    CFSG.PreuniquenessRankFour.Helpers.subgroup_normalizes_pCoreOf 2 (H ⊓ c.S.M)
  have hinf : H ⊓ Subgroup.normalizer ((CFSG.Open.pCoreOf 2 (H ⊓ c.S.M)) : Set G) =
      H ⊓ c.S.M := by
    apply le_antisymm
    · exact le_inf inf_le_left (inf_le_right.trans hNS)
    · exact le_inf inf_le_left hHM_N
  refine ⟨⟨hSH, hS1, ?_⟩, t.charTwo_of_isCalH hη hY hH, ?_⟩
  · rw [hinf]
  · apply le_antisymm
    · rw [CFSG.Quasithin.cgsIn]
      apply iSup_le
      intro C
      apply iSup_le
      intro hCS
      apply iSup_le
      intro hC1
      apply iSup_le
      intro hCc
      exact le_inf inf_le_left
        ((le_inf inf_le_left (inf_le_right.trans (hSC C hCS hC1 hCc))).trans hHM_N)
    · exact CFSG.Quasithin.inf_normalizer_le_cgsIn hS1

end CaseTwoTransitive

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
