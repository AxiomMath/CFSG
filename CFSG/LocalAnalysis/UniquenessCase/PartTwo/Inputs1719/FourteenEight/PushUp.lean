module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.NotThinShapes
public import CFSG.Quasithin.Recognition.Stroth.Str83RqO4Wiring
import CFSG.ClassicalGroups.PCoreSection
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FourteenEight.Components
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FourteenEight.OTwoQuot
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FourteenEight.Shape
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FourteenEight.SylowCent
import CFSG.LocalAnalysis.EvenBN.GMSK.SzFacts
import CFSG.LocalAnalysis.QuasithinUnique.CharTwoTransport
import CFSG.LocalAnalysis.RankThreeUC.SourceSetting.TwoGroupNormalizerMaxLocal.TwoGroupNormalizerMaxLocal
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen3a

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FourteenEight

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.LocalAnalysis.RankThreeUC.SourceSetting
open CFSG.LocalAnalysis.RankThreeUC.SourceSetting.TwoGroupNormalizerMaxLocal

variable {G : Type} [Group G] [Finite G]

private theorem le_centOverO2_of_map_conj {M L : Subgroup G} {t : G} (hL : L ∈ calC M)
    (htM : t ∈ M) (hne : L.map (MulAut.conj t).toMonoidHom ≠ L) :
    L.map (MulAut.conj t).toMonoidHom ≤ F08.CentOverO2 M L := by
  rintro _ ⟨l, hl, rfl⟩
  rw [PartTwo.mem_centOverO2_iff]
  refine ⟨M.mul_mem (M.mul_mem htM (hL.1.le hl)) (M.inv_mem htM), ?_⟩
  intro l' hl'
  have hmem := (PartTwo.calC_commutator_le_of_ne (map_conj_mem_calC hL htM) hL hne
    (Subgroup.commutator_mem_commutator (Subgroup.mem_map_of_mem _ hl) hl')).2
  rwa [commutatorElement_def] at hmem

omit [Finite G] in
private theorem pCoreOf_le_of_maximal {M L R : Subgroup G} (hLM : L ≤ M) (hR : IsPGroup 2 R)
    (hRM : R ≤ M) (hLR : L ≤ normalizer (R : Set G))
    (hmax : ∀ R' : Subgroup G, IsPGroup 2 R' → R' ≤ M → L ≤ normalizer (R' : Set G) →
      R ≤ R' → R' = R) :
    pCoreOf 2 M ≤ R := by
  have h2 : IsPGroup 2 (pCoreOf 2 M ⊔ R : Subgroup G) :=
    IsPGroup.to_sup_of_normal_left' (CFSG.ClassicalGroups.PCoreSection.isPGroup_pCoreOf 2 M) hR
      (hRM.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M))
  have hM : pCoreOf 2 M ⊔ R ≤ M :=
    sup_le (CFSG.ClassicalGroups.PCoreSection.pCoreOf_le 2 M) hRM
  have hN : L ≤ normalizer ((pCoreOf 2 M ⊔ R : Subgroup G) : Set G) :=
    (le_inf (hLM.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M)) hLR).trans
      (Subgroup.inf_normalizer_le_normalizer_sup (pCoreOf 2 M) R)
  have hEq : pCoreOf 2 M ⊔ R = R := hmax (pCoreOf 2 M ⊔ R) h2 hM hN le_sup_right
  exact hEq ▸ le_sup_left

theorem uniqueMax_conjClosure_of_ncard_eq_two {D : Data G} (h869 : F08.R869 D) {L : Subgroup G}
    (hL : L ∈ calC D.M) (h2 : (conjSetOf D.M L).ncard = 2) :
    UniqueMax D.M (conjClosure D.M L) := by
  obtain ⟨hXM, hMX, hprod⟩ :=
    uc22p22u_conjClosure_isProd (M := D.M) (X := D.M) (K := L) le_rfl Subgroup.le_normalizer hL
  have hnt : ¬ F08.Thin8 (conjClosure D.M L) :=
    S17.not_thin8_of_conjClosure_ne hL rfl (conjClosure_ne_of_ncard_eq_two h2)
  have hN : calNOf (conjClosure D.M L) = {D.M} :=
    h869 _ (Or.inr ⟨hXM, hMX, hprod⟩) _ le_rfl
      (sup_eq_left.mpr (CFSG.LieType.BorelTits.pCoreOf_le 2 _)) hnt
  exact uc22p22u_uniqueMax_of_calN D hXM hN

theorem exists_char_normal_of_isSz {K R : Subgroup G} {n : ℕ}
    (hSz : IsSz (Bar2 K) n) (hR : IsPGroup 2 R) (hRK : R ≤ normalizer (K : Set G))
    (hC : CFSG.QuasithinUnique.CharTwo (K ⊔ R))
    (hT : CFSG.QuasithinUnique.IsSylowTwoOf R (K ⊔ R)) :
    ∃ C : Subgroup G, C ≤ R ∧ C ≠ ⊥ ∧ (C.subgroupOf R).Characteristic ∧
      K ⊔ R ≤ normalizer (C : Set G) := by
  obtain ⟨a, ha, -, ⟨e⟩⟩ :=
    CFSG.LocalAnalysis.EvenBN.GMSK.exists_mulEquiv_sz_of_lieModel_twistedB2 hSz
  obtain ⟨e'⟩ := nonempty_oTwoQuot_sup_mulEquiv hSz hR hRK
  have h := CFSG.Quasithin.Stroth.Rq.not_noCharNormal_of_sz ha ⟨e'.trans e⟩ hC hT
  simp only [CFSG.QuasithinUnique.Setup.Campbell.NoCharNormal, not_forall, not_not] at h
  obtain ⟨C, hCR, hC1, hCc, hN⟩ := h
  exact ⟨C, hCR, hC1, hCc, hN⟩

theorem normalizer_le_of_maximal {D : Data G} (h869 : F08.R869 D)
    {L : Subgroup G} (hL : L ∈ calC D.M) (h2 : (conjSetOf D.M L).ncard = 2) {n : ℕ}
    (hSz : IsSz (Bar2 L) n) {R : Subgroup G} (hR : IsPGroup 2 R) (hRM : R ≤ D.M)
    (hLR : L ≤ normalizer (R : Set G))
    (hmax : ∀ R' : Subgroup G, IsPGroup 2 R' → R' ≤ D.M → L ≤ normalizer (R' : Set G) →
      R ≤ R' → R' = R) :
    normalizer (R : Set G) ≤ D.M := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, htM, hLtne, hconj⟩ := exists_conj_of_ncard_eq_two h2
  set K : Subgroup G := L.map (MulAut.conj t).toMonoidHom with hKdef
  have hKM : K ≤ D.M := by
    rw [hKdef]
    rintro _ ⟨l, hl, rfl⟩
    exact D.M.mul_mem (D.M.mul_mem htM (hL.1.le hl)) (D.M.inv_mem htM)
  have hconjK : conjSetOf D.M L = {L, K} := by
    rw [hconj, hKdef]
  have hSzK : IsSz (Bar2 K) n := by
    rw [hKdef]
    exact isSz_bar2_map_conj hSz t
  have hKcent : K ≤ F08.CentOverO2 D.M L := by
    rw [hKdef]
    exact le_centOverO2_of_map_conj hL htM hLtne
  have hRsyl : CFSG.ABGLocalTools.IsSylowOf 2 R (F08.CentOverO2 D.M L) :=
    isSylowOf_centOverO2_of_maximal hL hR hRM hLR hmax
  have hRC : R ≤ F08.CentOverO2 D.M L := hRsyl.le
  have hRnL : R ≤ normalizer (L : Set G) := hRC.trans (centOverO2_le_normalizer D.M L)
  have hRnK : R ≤ normalizer (K : Set G) := by
    rw [hKdef]
    exact (le_inf hRM hRnL).trans (inf_normalizer_le_normalizer_of_conjSetOf_eq hconj hLtne)
  have hKRC : K ⊔ R ≤ F08.CentOverO2 D.M L := sup_le hKcent hRC
  have hKR_sylow : CFSG.ABGLocalTools.IsSylowOf 2 R (K ⊔ R) :=
    hRsyl.of_le le_sup_right hKRC
  have hKR_sylowTwo : CFSG.QuasithinUnique.IsSylowTwoOf R (K ⊔ R) :=
    CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf.2 hKR_sylow
  have hOleR : pCoreOf 2 D.M ≤ R :=
    pCoreOf_le_of_maximal hL.1.le hR hRM hLR hmax
  have hCharM : CFSG.QuasithinUnique.CharTwo D.M := D.standing.charTwo D.M D.maxLocal.1
  have hCharKR : CFSG.QuasithinUnique.CharTwo (K ⊔ R) :=
    CFSG.QuasithinUnique.CharTwo.of_pCoreOf_le hCharM (sup_le hKM hRM)
      (hOleR.trans le_sup_right)
  obtain ⟨C, hCR, hCne, hCchar, hKRN⟩ :=
    exists_char_normal_of_isSz hSzK hR hRnK hCharKR hKR_sylowTwo
  have hNR : normalizer (R : Set G) ≤ normalizer (C : Set G) := by
    have : (C.subgroupOf R).Characteristic := hCchar
    have h := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (C.subgroupOf R)
    rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hCR] at h
  have hLNC : L ≤ normalizer (C : Set G) := hLR.trans hNR
  have hKNC : K ≤ normalizer (C : Set G) := le_sup_left.trans hKRN
  have hclosure : conjClosure D.M L ≤ normalizer (C : Set G) := by
    rw [conjClosure_eq_sup_of_conjSetOf_eq hconjK]
    exact sup_le hLNC hKNC
  have huniq : maxTwoLocalsContaining (conjClosure D.M L) = {D.M} := by
    simpa only [UniqueMax, calMOf, maxTwoLocalsContaining]
      using uniqueMax_conjClosure_of_ncard_eq_two h869 hL h2
  have hCM : normalizer (C : Set G) ≤ D.M :=
    normalizer_le_of_maxTwoLocalsContaining_eq_singleton hCne (hR.to_le hCR) hclosure huniq
  exact hNR.trans hCM

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FourteenEight
