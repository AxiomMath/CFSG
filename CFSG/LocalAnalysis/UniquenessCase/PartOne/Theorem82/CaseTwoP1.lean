module


public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoG1
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoG2
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputP1
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoShapeB
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoEta
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoMu
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoDnRank
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoDn
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoCoprimeSix
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoSolO
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoOStar
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoDnK11
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoDnBlock
import CFSG.GroupTheory.PCore.NormalPCoreOf

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open Subgroup

variable {G : Type} [Group G] [Finite G]

namespace CaseTwoTransitive

variable {c : Ctx812E G} (t : CaseTwoTransitive c)

theorem uniqueTwoLocalKy (hK11 : K11) (hK32 : CFSG.LocalAnalysis.UniquenessCase.UCK.K32)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hSp : CFSG.CGT.PushingUpLit.CGT6.SporadicThreeCenterSmallPrimes)
    (hK332 : CFSG.LocalAnalysis.UniquenessCase.UCK.K332ThreeAb) (hOut : PerfectAutInner)
    (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier)
    (hNT : CFSG.AGLEmbedding.Asc81bNineThree) (hblk : CFSG.AGLEmbedding.AschbacherLocalCGTBlock)
    (hKF1 : L3NotEvenClassical) (hKF2 : L3EvenParabolic) {p : ℕ}
    (hp : p ∈ c.sig)
    (hN : t.PairNormalizerLe p)
    (hZ : Subgroup.centralizer (t.Z : Set G) ≤ c.S.M) : t.UniqueTwoLocalKy := by
  classical
  haveI := c.standing.simple
  by_contra hne
  obtain ⟨Y, hY⟩ := t.exists_isMuStar hne
  have hYM : Y ≤ c.S.M := hY.1.1
  have hKY : t.Ky ≤ Y :=
    calc t.Ky ≤ t.Ky ⊔ CFSG.Open.pCoreOf 2 Y := le_sup_left
      _ = Y := hY.1.2.1.symm
  have hYU : ¬ UniqueTwoLocal c.S.M Y := hY.1.2.2.2
  simp only [UniqueTwoLocal, not_forall] at hYU
  obtain ⟨N, hNIso, hYN, hNM⟩ := hYU
  have hKN : t.Ky ≤ N := hKY.trans hYN
  have hZN : t.Z ≤ N := t.Z_le_Ky.trans hKN
  have hNtop : N ≠ ⊤ := CFSG.PreuniquenessRankFour.Helpers.twoLocal_ne_top c.standing.nonab hNIso
  have hrank := t.pRank_Dn hK332 hOut hp hN hZ hNIso hNM hZN
  have hDM := t.not_Dn_le hp hN hZ hZN hNM hrank
  obtain ⟨H, hDH, hYH, hHN⟩ : ∃ H : Subgroup G, t.Dn N ≤ H ∧ Y ≤ H ∧ H ≤ N :=
    ⟨t.Dn N ⊔ Y, le_sup_left, le_sup_right, sup_le (t.Dn_le N) hYN⟩
  have hO2 : CFSG.Open.pCoreOf 2 (t.Dn N) ≤ CFSG.Open.pCoreOf 2 H :=
    CFSG.GroupTheory.pCoreOf_le_pCoreOf_of_le_normalizer 2 hDH (hHN.trans (t.le_normalizer_Dn N))
  have hCalH : IsCalH c.S.M Y H := ⟨hYH, fun h => hDM (hDH.trans h),
    fun h => t.pCoreOf_Dn_ne_bot hNIso hZN (eq_bot_iff.mpr (hO2.trans h.le))⟩
  have hη := t.kyInEta hK32 hGA hSp hp hN hZ
  have hHyp := t.asc81bHyp_of_isCalH hη hY hCalH
  have hQS : CFSG.Open.pCoreOf 2 H ≤ CFSG.Open.pCoreOf 2 (H ⊓ c.S.M) :=
    t.pCoreOf_le_of_isCalH hη hY hCalH
  have hYS : Y ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 (H ⊓ c.S.M) : Set G) :=
    (le_inf hYH hYM).trans
      (CFSG.LocalAnalysis.UniquenessCase.UC6.le_normalizer_pCoreOf 2 (H ⊓ c.S.M))
  have hS2 : IsPGroup 2 (CFSG.Open.pCoreOf 2 (H ⊓ c.S.M)) := by
    rw [CFSG.openPCoreOf_eq_map_pCore]
    exact (CFSG.pCore_isPGroup (p := 2) (G := ↥(H ⊓ c.S.M))).map _
  have hSH : CFSG.Open.pCoreOf 2 (H ⊓ c.S.M) ≤ H :=
    (CFSG.openPCoreOf_le 2 (H ⊓ c.S.M)).trans inf_le_left
  have hSR : CFSG.Open.pCoreOf 2 (H ⊓ c.S.M) ≤ CFSG.Open.pCoreOf 2 Y :=
    t.le_pCoreOf_of_isCalH hη hY hCalH hS2 hSH hYS
  have hSC : ∀ C : Subgroup G, C ≤ CFSG.Open.pCoreOf 2 (H ⊓ c.S.M) → C ≠ ⊥ →
      (C.subgroupOf (CFSG.Open.pCoreOf 2 (H ⊓ c.S.M))).Characteristic →
      Subgroup.normalizer (C : Set G) ≤ c.S.M := fun C hC hC1 hCc =>
    t.normalizer_le_of_le_of_isCalH hη hY hCalH le_rfl hSR hYS hC hC1 hCc
  have hSne : CFSG.Open.pCoreOf 2 (H ⊓ c.S.M) ≠ ⊥ := fun h =>
    hCalH.2.2 (eq_bot_iff.mpr (hQS.trans h.le))
  have hSM : Subgroup.normalizer (CFSG.Open.pCoreOf 2 (H ⊓ c.S.M) : Set G) ≤ c.S.M :=
    hSC _ le_rfl hSne (by rw [Subgroup.subgroupOf_self]; infer_instance)
  have hCT := t.charTwo_of_isCalH hη hY hCalH
  have h528 : ∀ X : Subgroup G, CFSG.Open.pCoreOf 2 H ≤ X → X ≤ H →
      H ≤ Subgroup.normalizer (X : Set G) →
      ¬ 2 ∣ ((CFSG.Open.pCoreOf 2 H).subgroupOf X).index →
      ¬ 3 ∣ ((CFSG.Open.pCoreOf 2 H).subgroupOf X).index → X ≤ c.S.M := by
    intro X hQX hXH hHX h2 h3
    have hXS : X ⊔ CFSG.Open.pCoreOf 2 (H ⊓ c.S.M) ≠ ⊤ := fun h =>
      hNtop (eq_top_iff.mpr (by rw [← h]; exact sup_le (hXH.trans hHN) (hSH.trans hHN)))
    exact le_of_index_coprime_six hblk hCT hS2 hSH hQS hSC
      (c.standing.kProper.isKGroup _ hXS) hQX hXH (hSH.trans hHX) h2 h3
  obtain ⟨hsolM, hsolc⟩ := t.sol_On_le hK32 hGA hSp hKN hDH hHN h528
  have hOsol := t.On_le_sol hK32 hGA hSp hSch hZ hNtop hKN hsolM
  have hO : t.On N ≤ c.S.M := hOsol.trans hsolM
  have hOeq : CFSG.SignalizerFunctorTheorem.McBride.sol (t.On N) = t.On N :=
    le_antisymm (Subgroup.map_subtype_le _) hOsol
  have hOc : ⁅t.Dn N, t.On N⁆ ≤ CFSG.Open.pCoreOf 2 (t.Dn N) := by
    rw [← hOeq]
    exact hsolc
  have hKS : t.Ky ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 (H ⊓ c.S.M) : Set G) :=
    hKY.trans hYS
  rcases t.Dhat_cases hK32 hGA hSp hNtop hKN hrank with h | h | h | h
  · exact hDM (t.Dn_le_of_K11 hK11 hK32 hGA hSp hp hN hZ hKN hrank hO (Or.inl h))
  · exact t.false_of_L3 hNT hKF1 hKF2 hK11 hK32 hGA hSp hp hN hZ hNIso hNM hKN hDH hHN hHyp hSM
      hKS hrank hDM hO hOc (Or.inl h)
  · exact t.false_of_L3 hNT hKF1 hKF2 hK11 hK32 hGA hSp hp hN hZ hNIso hNM hKN hDH hHN hHyp hSM
      hKS hrank hDM hO hOc (Or.inr h)
  · exact hDM (t.Dn_le_of_K11 hK11 hK32 hGA hSp hp hN hZ hKN hrank hO (Or.inr h))

theorem caseTwoResidual_of_c4Data (X : C4Data G c.S.M)
    (hK11 : K11) (hK32 : CFSG.LocalAnalysis.UniquenessCase.UCK.K32)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hSp : CFSG.CGT.PushingUpLit.CGT6.SporadicThreeCenterSmallPrimes)
    (hK332 : CFSG.LocalAnalysis.UniquenessCase.UCK.K332ThreeAb) (hOut : PerfectAutInner)
    (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier)
    (hNT : CFSG.AGLEmbedding.Asc81bNineThree) (hblk : CFSG.AGLEmbedding.AschbacherLocalCGTBlock)
    (hKF1 : L3NotEvenClassical) (hKF2 : L3EvenParabolic)
    (hK461 : CFSG.LocalAnalysis.UniquenessCase.UCK.K461)
    (hK462 : CFSG.LocalAnalysis.UniquenessCase.UCK.K462)
    (hK49 : CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.K49I)
    (hST : CFSG.CGT.PushingUpLit.SolKNA.SolomonTimmesfeldMainRankGe2) (hL3 : L3Overgroup)
    (hSE : CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.StronglyEmbeddedFive) :
    t.CaseTwoResidual := by
  intro p hp h76 hN hIIa hZ hrank
  have hP1 := t.uniqueTwoLocalKy hK11 hK32 hGA hSp hK332 hOut hSch hNT hblk hKF1 hKF2
    hp hN hZ
  exact t.caseTwoResidual_of_G1_G2 hK11 hK32 hGA hSp hK332 hOut
    (t.caseTwoG1_of_uniqueTwoLocalKy X hK461 hK462 hK49 hST hSch hK32 hGA hSp hK332 hOut hP1)
    (t.caseTwoG2_of_uniqueTwoLocalKy hL3 hK32 hGA hSp hK332 hOut hSE hP1) p hp h76 hN hIIa hZ hrank

section Full

variable {c : Ctx812 G} (t : CaseTwoTransitive c.toCtx812E)

theorem caseTwoResidual_of_inputs (hK11 : K11) (hK32 : CFSG.LocalAnalysis.UniquenessCase.UCK.K32)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hSp : CFSG.CGT.PushingUpLit.CGT6.SporadicThreeCenterSmallPrimes)
    (hK332 : CFSG.LocalAnalysis.UniquenessCase.UCK.K332ThreeAb) (hOut : PerfectAutInner)
    (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier)
    (hNT : CFSG.AGLEmbedding.Asc81bNineThree) (hblk : CFSG.AGLEmbedding.AschbacherLocalCGTBlock)
    (hKF1 : L3NotEvenClassical) (hKF2 : L3EvenParabolic)
    (hK461 : CFSG.LocalAnalysis.UniquenessCase.UCK.K461)
    (hK462 : CFSG.LocalAnalysis.UniquenessCase.UCK.K462)
    (hK49 : CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.K49I)
    (hST : CFSG.CGT.PushingUpLit.SolKNA.SolomonTimmesfeldMainRankGe2) (hL3 : L3Overgroup)
    (hSE : CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.StronglyEmbeddedFive) :
    t.CaseTwoResidual :=
  t.caseTwoResidual_of_c4Data c.c4 hK11 hK32 hGA hSp hK332 hOut hSch hNT hblk hKF1 hKF2
    hK461 hK462 hK49 hST hL3 hSE

end Full

end CaseTwoTransitive

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
