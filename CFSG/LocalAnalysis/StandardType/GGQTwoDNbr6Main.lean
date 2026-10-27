module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDNbr6Defs
public import CFSG.LocalAnalysis.StandardType.GGQTwoDNbr6Rows
public import CFSG.LocalAnalysis.StandardType.GGQTwoDNbr6Orth
public import CFSG.LocalAnalysis.StandardType.GGQTwoDNbr6U6
public import CFSG.LocalAnalysis.StandardType.GGQTwoDNbrMain

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Assembly CFSG.Blueprint CFSG.ClassicalInvolution.Phan

theorem qtwoDNbr6_chart4_or {R : ℕ → Prop} (hR : ∀ m, R m → 6 ≤ m)
    (hRM : GGQTwoRMInputOn R) (hTCJ : GGTCJKnown) (hLB : GGLBalanceInput)
    (hPJ : GGStdSubPrimeInput) (hSel : GGQTwoDSelModuleInputOn R) (hTw : GGQTwoDSixTwE6InputOn R)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)} (hcfg : GGQTwoDCfg p B Bs x L D J 𝒦 M e)
    {m : ℕ} (e' : Fin m ≃ ι) (hRm : R m) (hM : M = (ggCoxeterMatrixD m).reindex e')
    (hJlab : ∃ labJ : LargeEvenLabel, LargeEvenInLambda2 labJ ∧
      GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J) ∧ labJ.n = 1 ∧ labJ.tag ≠ .A ∧
        (labJ.tag = .twD → labJ.rank ≠ 2))
    {y : G} {X : Subgroup G} (hnbr : GGNbr p B x D J y X) :
    QTwoDL1Chart4 p B Bs X ∨ (m = 6 ∧ B = Bs ∧ GGInnerDiagOnLabel (fun p lab =>
      ggRowP_ESU p lab ∧ lab.n = 1 ∧ lab.rank = 5) p Bs X) := by
  have hm : 6 ≤ m := hR m hRm
  obtain ⟨r, hr, hrc, h6⟩ := hcfg.2.2.2.2
  have hp3 : p = 3 := ggQTwo_p_eq_three hcfg.1 M e hcfg.2.2.2.1 hr hrc h6
  subst hp3
  have hroute : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦 := hcfg.1
  have hconf : GGConfig 3 B Bs x L D J := hroute.1.1
  have hpres : GGCoxeterPres 3 (ggAutomizerJoin L Bs 𝒦) M e := hcfg.2.2.2.1
  have hD : GGIsWeylMatrixD M := ⟨m, e', by omega, hM⟩
  have hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3 := GGIsWeylMatrixAD.le_three (Or.inr hD)
  have hA : ggAutomizer X Bs ≤ ggAutomizerJoin L Bs 𝒦 :=
    hRM G 3 B Bs x L D J 𝒦 ι M e hcfg m e' hRm hM y X hnbr
  obtain ⟨β, hβ⟩ := hSel G 3 B Bs x L D J 𝒦 ι M e hcfg m e' hRm hM
  have hcard : Nat.card ↥Bs = 3 ^ m := card_bs_of_module β
  have hcent := qtwoDNbr_card_cent_le hconf hnbr
  have hInn : GGInnerDiagOn Bs X := hroute.1.2.2.1.2 y X hnbr
  have hrkm : ∀ hN : Bs ≤ Subgroup.normalizer (X : Set G),
      3 ^ (m - 2) ≤ Nat.card (ggGamma X hN).range := fun hN =>
    three_pow_le_card_range_gamma hcard hcent hN
  have hrk4 : ∀ hN : Bs ≤ Subgroup.normalizer (X : Set G),
      3 ^ 4 ≤ Nat.card (ggGamma X hN).range := fun hN =>
    (Nat.pow_le_pow_right (by norm_num) (by omega : 4 ≤ m - 2)).trans (hrkm hN)
  have hTw5 : GGInnerDiagOnLabel (fun p lab => ggRowP_ETwE6 p lab ∧ p = 3) 3 Bs X →
      ∀ hN : Bs ≤ Subgroup.normalizer (X : Set G), 3 ^ 5 ≤ Nat.card (ggGamma X hN).range := by
    intro hmk hN
    by_cases hm6 : m = 6
    · exact hTw G 3 B Bs x L D J 𝒦 ι M e hcfg m e' hRm hm6 hM y X hnbr hmk hN
    · exact (Nat.pow_le_pow_right (by norm_num) (by omega : 5 ≤ m - 2)).trans (hrkm hN)
  have hJX : J ≤ X :=
    le_of_ggNbr hLB hconf.1 hconf.2.2 (hPJ G 3 B x L D J hconf.1 hconf.2.2) hnbr
  obtain ⟨labJ, hΛJ, hhasJ, hnJ, htagJ, htwDJ⟩ := hJlab
  have hfield := qtwoDNbr_field ggLabelRigidInput_holds hTCJ hconf hnbr hJX hInn hΛJ hhasJ hnJ
    htagJ htwDJ
  have hns : ¬ GGSplitLie 3 X := qtwoDNbr_nonSplit hfield
  have hmark := qtwoDNbr6_rows ggLabelRigidInput_holds hroute hpres hD hnbr hA hns hfield hrk4
    hTw5
  have hFix : QTwoDFixBound Bs X m := qtwoDNbr_fixBound hroute hpres (by omega) hle3 e' β hβ hA
  have hsplit : GGInnerDiagOnLabel (fun p lab => (ggRowP_ESU p lab ∧ lab.n = 1) ∨
      ((ggRowP_EOmP p lab ∨ ggRowP_EOmM p lab) ∧ lab.n = 1)) 3 Bs X :=
    GGInnerDiagOnLabel.mono' (fun lab ⟨hl, hn⟩ => by
      rcases hl with hl | hl | hl
      · exact Or.inl ⟨hl, hn⟩
      · exact Or.inr ⟨Or.inl hl, hn⟩
      · exact Or.inr ⟨Or.inr hl, hn⟩) hmark
  rcases GGInnerDiagOnLabel.elim_or hsplit with hU | hO
  · rcases qtwoDNbr6_esu_or ggSecFiveNSCornerInput_holds hroute hnbr hJX (Or.inl hm) hcard hFix
      hU with h | h
    · exact Or.inl h.toChart4
    · exact Or.inr h
  · obtain ⟨Φ, hF, h4, hlt, hZ⟩ :=
      qtwoDNbr6_orth ggLabelRigidInput_holds hconf hnbr hcard (Or.inl hm) hcent hO
    exact Or.inl (Or.inr ⟨Φ, hF, h4, hlt, hZ⟩)

end CFSG.StandardType.QTwo

end
