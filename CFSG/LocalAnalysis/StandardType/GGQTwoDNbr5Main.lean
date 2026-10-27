module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDGN6Assembly
import CFSG.LocalAnalysis.StandardType.GGQTwoDNbr6Rows
import CFSG.LocalAnalysis.StandardType.GGQTwoDNbr6Orth
import CFSG.LocalAnalysis.StandardType.GGQTwoDNbr6U6
import CFSG.LocalAnalysis.StandardType.GGQTwoDNbr6TwE6
import CFSG.LocalAnalysis.StandardType.GGQTwoDNbrField
import CFSG.LocalAnalysis.StandardType.GGQTwoDNbrFix
import CFSG.LocalAnalysis.StandardType.GGF4ThreeSCCube
import CFSG.LocalAnalysis.StandardType.GGF4ThreeSCCubeHolds
import CFSG.LocalAnalysis.StandardType.GGQTwoDL1PrimeToThree
import CFSG.LocalAnalysis.StandardType.GGQTwoDSelModuleOfB2
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitBaseThm
import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthChart
import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthTorJ
import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthTorHolds
import CFSG.LocalAnalysis.StandardType.GGQTwoDSevenPrelim
import CFSG.LocalAnalysis.StandardType.GGLabelRigid
import CFSG.LocalAnalysis.StandardType.GGSecFiveNSCornerMain
import CFSG.LocalAnalysis.StandardType.GGQTwoDSelBases

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Assembly CFSG.Blueprint CFSG.ClassicalInvolution.Phan

section Or


theorem GGQTwoGNInputOn.or {R R' : ℕ → Prop} (h : GGQTwoGNInputOn R) (h' : GGQTwoGNInputOn R') :
    GGQTwoGNInputOn fun m => R m ∨ R' m := by
  intro G _ _ p B Bs x L D J 𝒦 ι M e hcfg m e' hm
  rcases hm with hm | hm
  · exact h G p B Bs x L D J 𝒦 ι M e hcfg m e' hm
  · exact h' G p B Bs x L D J 𝒦 ι M e hcfg m e' hm

end Or

section Five


theorem qtwoD5_jlabel (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput) {G : Type} [Group G]
    [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hcfg : GGQTwoDCfg 3 B Bs x L D J 𝒦 M e) (e' : Fin 5 ≃ ι)
    (hM : M = (ggCoxeterMatrixD 5).reindex e') :
    ∃ labJ : LargeEvenLabel, LargeEvenInLambda2 labJ ∧
      GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J) ∧ labJ.n = 1 ∧ labJ.tag ≠ .A ∧
        (labJ.tag = .twD → labJ.rank ≠ 2) := by
  by_cases hcell : qtwoOrthL G L 𝒦
  · obtain ⟨lab, hΛ, hhas, hn, htag⟩ := hcell
    obtain ⟨Φ, hF, -, h4, hZ, -⟩ :=
      qtwoOrthFrameCore_of_cfg hcfg (qtwo_label_le_three e' hM) hΛ hhas hn htag
    exact qtwoOrth_jlabel_of_frame hcfg.1 Φ hF h4 hZ
  · obtain ⟨F0, iF, iFin, iC, ψ, ε, h⟩ := ggQTwoDUnit_base_of_ne_six ggLabelRigidInput_holds hTBF
      hWI hcfg e' (by norm_num) (by norm_num) hM hcell
    exact qtwoDNbr_jlabel ggQTwoDOrthJInput_holds hcfg.1
      (Or.inl ⟨F0, iF, iFin, iC, 5, ψ, h.card_field, h.hyp, h.range, h.diag,
        h.card_bs_eq (by norm_num)⟩)

theorem qtwoDNbr5_chart4 (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput)
    (hRM : GGQTwoRMInputOn fun m => m = 5) (hTCJ : GGTCJKnown) (hLB : GGLBalanceInput)
    (hPJ : GGStdSubPrimeInput) (hRk : GGTwE6ThreeNbrRankInput) {G : Type} [Group G] [Finite G]
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hcfg : GGQTwoDCfg p B Bs x L D J 𝒦 M e) (e' : Fin 5 ≃ ι)
    (hM : M = (ggCoxeterMatrixD 5).reindex e') {y : G} {X : Subgroup G}
    (hnbr : GGNbr p B x D J y X) : QTwoDL1Chart4 p B Bs X := by
  obtain ⟨r, hr, hrc, h6⟩ := hcfg.2.2.2.2
  have hp3 : p = 3 := ggQTwo_p_eq_three hcfg.1 M e hcfg.2.2.2.1 hr hrc h6
  subst hp3
  have hroute : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦 := hcfg.1
  have hconf : GGConfig 3 B Bs x L D J := hroute.1.1
  have hpres : GGCoxeterPres 3 (ggAutomizerJoin L Bs 𝒦) M e := hcfg.2.2.2.1
  have hD : GGIsWeylMatrixD M := ⟨5, e', by norm_num, hM⟩
  have hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3 := GGIsWeylMatrixAD.le_three (Or.inr hD)
  have hA : ggAutomizer X Bs ≤ ggAutomizerJoin L Bs 𝒦 :=
    hRM G 3 B Bs x L D J 𝒦 ι M e hcfg 5 e' rfl hM y X hnbr
  obtain ⟨β, hβ⟩ := ggQTwoDSelModuleInputOn_of_selectedModule (R := fun m => m = 5)
    (fun m hm => by omega) hTBF hWI G 3 B Bs x L D J 𝒦 ι M e hcfg 5 e' rfl hM
  have hcard : Nat.card ↥Bs = 3 ^ 5 := card_bs_of_module β
  have hcent := qtwoDNbr_card_cent_le hconf hnbr
  have hInn : GGInnerDiagOn Bs X := hroute.1.2.2.1.2 y X hnbr
  have hlt : B < Bs :=
    ggQTwoD_B_lt_Bs_of_not_three_dvd hTBF hWI hcfg e' (by norm_num) (by norm_num) hM
  have hJX : J ≤ X :=
    le_of_ggNbr hLB hconf.1 hconf.2.2 (hPJ G 3 B x L D J hconf.1 hconf.2.2) hnbr
  obtain ⟨labJ, hΛJ, hhasJ, hnJ, htagJ, htwDJ⟩ := qtwoD5_jlabel hTBF hWI hcfg e' hM
  have hfield := qtwoDNbr_field ggLabelRigidInput_holds hTCJ hconf hnbr hJX hInn hΛJ hhasJ hnJ
    htagJ htwDJ
  have hmark := qtwoDNbr_rows_of_noF4 ggLabelRigidInput_holds hroute hpres hD hnbr hA
    (qtwoDNbr_nonSplit hfield) hfield
    (ggRow_absurd_F4Three_of_cube ggF4ThreeSCCubeInput_holds hroute hpres hle3 hA)
    (qtwoDNbr_twE6_rank hRk hconf hnbr)
  have hFix : QTwoDFixBound Bs X 5 := qtwoDNbr_fixBound hroute hpres (by norm_num) hle3 e' β hβ hA
  have hsplit : GGInnerDiagOnLabel (fun p lab => (ggRowP_ESU p lab ∧ lab.n = 1) ∨
      ((ggRowP_EOmP p lab ∨ ggRowP_EOmM p lab) ∧ lab.n = 1)) 3 Bs X :=
    GGInnerDiagOnLabel.mono' (fun lab ⟨hl, hn⟩ => by
      rcases hl with hl | hl | hl
      · exact Or.inl ⟨hl, hn⟩
      · exact Or.inr ⟨Or.inl hl, hn⟩
      · exact Or.inr ⟨Or.inr hl, hn⟩) hmark
  rcases GGInnerDiagOnLabel.elim_or hsplit with hU | hO
  · rcases qtwoDNbr6_esu_or ggSecFiveNSCornerInput_holds hroute hnbr hJX (Or.inr hlt) hcard hFix
      hU with h | h
    · exact h.toChart4
    · exact absurd h.2.1 hlt.ne
  · obtain ⟨Φ, hF, h4, hlt4, hZ⟩ := qtwoDNbr6_orth ggLabelRigidInput_holds hconf hnbr hcard
      (Or.inr ⟨by norm_num, hlt⟩) hcent hO
    exact Or.inr ⟨Φ, hF, h4, hlt4, hZ⟩

theorem ggQTwoDL1Chart4NbrInputOn_five (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput)
    (hRM : GGQTwoRMInputOn fun m => m = 5) (hTCJ : GGTCJKnown) (hLB : GGLBalanceInput)
    (hPJ : GGStdSubPrimeInput) (hRk : GGTwE6ThreeNbrRankInput) :
    GGQTwoDL1Chart4NbrInputOn fun m => m = 5 := by
  intro G _ _ p B Bs x L D J 𝒦 ι M e hcfg m e' hm hM y X hnbr
  subst hm
  exact qtwoDNbr5_chart4 hTBF hWI hRM hTCJ hLB hPJ hRk hcfg e' hM hnbr

theorem ggQTwoGNInputOn_five (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput)
    (hRM : GGQTwoRMInputOn fun m => m = 5) (hTCJ : GGTCJKnown) (hLB : GGLBalanceInput)
    (hPJ : GGStdSubPrimeInput) (hRk : GGTwE6ThreeNbrRankInput) :
    GGQTwoGNInputOn fun m => m = 5 :=
  ggQTwoGNInputOn_of_inputs4 hLB hPJ
    (ggQTwoDL1Chart4NbrInputOn_five hTBF hWI hRM hTCJ hLB hPJ hRk) qTwoOrthJAnchor4Input_holds

end Five

end CFSG.StandardType.QTwo

end
