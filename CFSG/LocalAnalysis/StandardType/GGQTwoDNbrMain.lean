module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDNbrDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoDNbrField
public import CFSG.LocalAnalysis.StandardType.GGQTwoDNbrRows
public import CFSG.LocalAnalysis.StandardType.GGQTwoDNbrOrth
public import CFSG.LocalAnalysis.StandardType.GGQTwoDNbrEsu
public import CFSG.LocalAnalysis.StandardType.GGQTwoDNbrFix
public import CFSG.LocalAnalysis.StandardType.GGQTwoDGen
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNSCornerMain
public import CFSG.LocalAnalysis.StandardType.GGNbrBalance

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Assembly CFSG.Blueprint CFSG.ClassicalInvolution.Phan

theorem ggQTwoDL1ChartNbrInput_of_inputs
    (hRM : GGQTwoRMInput) (hL : GGQTwoDL1ChartLInput) (hTCJ : GGTCJKnown)
    (hLB : GGLBalanceInput) (hPJ : GGStdSubPrimeInput) (hSel : GGQTwoDSelModuleInput)
    (hOJ : GGQTwoDOrthJInput) : GGQTwoDL1ChartNbrInput := by
  intro G _ _ p B Bs x L D J 𝒦 ι M e hcfg m e' hm hM y X hnbr
  obtain ⟨r, hr, hrc, h6⟩ := hcfg.2.2.2.2
  have hp3 : p = 3 := ggQTwo_p_eq_three hcfg.1 M e hcfg.2.2.2.1 hr hrc h6
  subst hp3
  have hroute : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦 := hcfg.1
  have hconf : GGConfig 3 B Bs x L D J := hroute.1.1
  have hpres : GGCoxeterPres 3 (ggAutomizerJoin L Bs 𝒦) M e := hcfg.2.2.2.1
  have hD : GGIsWeylMatrixD M := ⟨m, e', by omega, hM⟩
  have hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3 := GGIsWeylMatrixAD.le_three (Or.inr hD)
  have hA : ggAutomizer X Bs ≤ ggAutomizerJoin L Bs 𝒦 :=
    hRM G 3 B Bs x L D J 𝒦 ι M e hcfg m e' hm hM y X hnbr
  obtain ⟨β, hβ⟩ := hSel G 3 B Bs x L D J 𝒦 ι M e hcfg m e' hm hM
  have hcard : Nat.card ↥Bs = 3 ^ m := card_bs_of_module β
  have hcent := qtwoDNbr_card_cent_le hconf hnbr
  have hInn : GGInnerDiagOn Bs X := hroute.1.2.2.1.2 y X hnbr
  have hrk : ∀ hN : Bs ≤ Subgroup.normalizer (X : Set G),
      3 ^ 5 ≤ Nat.card (ggGamma X hN).range := fun hN =>
    (Nat.pow_le_pow_right (by norm_num) (by omega : 5 ≤ m - 2)).trans
      (three_pow_le_card_range_gamma hcard hcent hN)
  have hJX : J ≤ X :=
    le_of_ggNbr hLB hconf.1 hconf.2.2 (hPJ G 3 B x L D J hconf.1 hconf.2.2) hnbr
  have hchartL : QTwoDL1Chart 3 B Bs L := hL G 3 B Bs x L D J 𝒦 ι M e hcfg m e' hm hM
  obtain ⟨labJ, hΛJ, hhasJ, hnJ, htagJ, htwDJ⟩ := qtwoDNbr_jlabel hOJ hroute hchartL
  have hfield := qtwoDNbr_field ggLabelRigidInput_holds hTCJ hconf hnbr hJX hInn hΛJ hhasJ hnJ
    htagJ htwDJ
  have hns : ¬ GGSplitLie 3 X := qtwoDNbr_nonSplit hfield
  have hmark := qtwoDNbr_rows ggLabelRigidInput_holds hroute hpres hD hnbr hA hns hfield hrk
  have hFix : QTwoDFixBound Bs X m := qtwoDNbr_fixBound hroute hpres (by omega) hle3 e' β hβ hA
  have hsplit : GGInnerDiagOnLabel (fun p lab => (ggRowP_ESU p lab ∧ lab.n = 1) ∨
      ((ggRowP_EOmP p lab ∨ ggRowP_EOmM p lab) ∧ lab.n = 1)) 3 Bs X :=
    GGInnerDiagOnLabel.mono' (fun lab ⟨hl, hn⟩ => by
      rcases hl with hl | hl | hl
      · exact Or.inl ⟨hl, hn⟩
      · exact Or.inr ⟨Or.inl hl, hn⟩
      · exact Or.inr ⟨Or.inr hl, hn⟩) hmark
  rcases GGInnerDiagOnLabel.elim_or hsplit with hU | hO
  · exact qtwoDNbr_esu ggSecFiveNSCornerInput_holds hroute hnbr hJX hm hcard hcent hFix hU
  · obtain ⟨Φ, hF, h5, hZ⟩ := qtwoDNbr_orth ggLabelRigidInput_holds hconf hcard hm hcent hO
    exact Or.inr ⟨Φ, hF, h5, hZ⟩

end CFSG.StandardType.QTwo

end
