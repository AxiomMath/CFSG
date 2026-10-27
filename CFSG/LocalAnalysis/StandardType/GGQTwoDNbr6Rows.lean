module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDNbr6Defs
public import CFSG.LocalAnalysis.StandardType.GGQTwoDNbrRows

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Assembly CFSG.Blueprint CFSG.ClassicalInvolution.Phan

variable {G : Type} [Group G] [Finite G]

theorem qtwoDNbr_rows_of_noF4
    (hRig : GGLabelRigidInput) {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦) {ι : Type}
    {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres 3 (ggAutomizerJoin L Bs 𝒦) M e) (hD : GGIsWeylMatrixD M) {y : G}
    {X : Subgroup G} (hnbr : GGNbr 3 B x D J y X)
    (hA : ggAutomizer X Bs ≤ ggAutomizerJoin L Bs 𝒦) (hns : ¬ GGSplitLie 3 X)
    (hn1 : ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab →
      GGHasLabel lab (↥X ⧸ Subgroup.center ↥X) → lab.n = 1)
    (hnoF4 : ¬ GGF4ThreeMarking Bs X)
    (hTw5 : GGInnerDiagOnLabel (fun p lab => ggRowP_ETwE6 p lab ∧ p = 3) 3 Bs X →
      ∀ hN : Bs ≤ Subgroup.normalizer (X : Set G), 3 ^ 5 ≤ Nat.card (ggGamma X hN).range) :
    GGInnerDiagOnLabel (fun p lab =>
      (ggRowP_ESU p lab ∨ ggRowP_EOmP p lab ∨ ggRowP_EOmM p lab) ∧ lab.n = 1) 3 Bs X := by
  have hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3 := GGIsWeylMatrixAD.le_three (Or.inr hD)
  have hweak : GGSecFiveWeakNbr 3 B Bs x L D J 𝒦 X := ⟨⟨y, hnbr⟩, hA⟩
  have hX : X = L ∨ ∃ y, GGNbr 3 B x D J y X := Or.inr ⟨y, hnbr⟩
  have hNP : GGNoReflE6Pat 3 Bs X := ggX_noReflE6Pat_typeD hcfg hpres hD hA
  have hEnn : GGInnerDiagOnLabel ggRowP_Ennola 3 Bs X :=
    ggX_ennola_of_nonSplit hcfg hpres hle3 (Or.inr hweak) hns
  have h1 : GGInnerDiagOnLabel (fun p lab => ggRowP_Ennola p lab ∧ lab.n = 1) 3 Bs X :=
    GGInnerDiagOnLabel.mono_label_of_hasLabel
      (fun lab hΛ hhas hrow => ⟨hrow, hn1 lab hΛ hhas⟩) hEnn
  have h2 : GGInnerDiagOnLabel (fun p lab => GGF4ThreeLabel p lab ∨
      ((ggRowP_ETwE6 p lab ∧ p = 3) ∨ ggRowP_EE7 p lab ∨ ggRowP_EE8 p lab ∨
        ((ggRowP_ESU p lab ∨ ggRowP_EOmP p lab ∨ ggRowP_EOmM p lab) ∧ lab.n = 1))) 3 Bs X :=
    h1.mono' fun lab ⟨hl, hn⟩ => by
      rcases hl with hl | ⟨hF, -, hd⟩
      · rcases hl with hl | hl | hl | hl | hl | hl
        · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨Or.inl hl, hn⟩)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨Or.inr (Or.inl hl), hn⟩)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨Or.inr (Or.inr hl), hn⟩)))
        · exact Or.inr (Or.inl ⟨hl, rfl⟩)
        · exact Or.inr (Or.inr (Or.inl hl))
        · exact Or.inr (Or.inr (Or.inr (Or.inl hl)))
      · exact Or.inl ⟨hF.1, rfl, hd⟩
  rcases GGInnerDiagOnLabel.elim_or h2 with hF4 | h3
  ·
    have hM : GGF4ThreeMarking Bs X := largeEvenMarking_mono (fun _ _ _ _ _ _ hP => hP) hF4
    exact (hnoF4 hM).elim
  rcases GGInnerDiagOnLabel.elim_or h3 with hTw | h4
  ·
    exact (ggX_row_absurd_of_noReflE6PatAt hRig (r := 5) (by norm_num) ggRowE6PatAt_ETwE6_three
      hcfg hX hNP (hTw5 hTw) hTw).elim
  rcases GGInnerDiagOnLabel.elim_or h4 with h7 | h5
  · exact (ggX_row_absurd_of_noReflE6Pat hRig ggRowE6Pat_EE7 hcfg hX hNP h7).elim
  rcases GGInnerDiagOnLabel.elim_or h5 with h8 | h6
  · exact (ggX_row_absurd_of_noReflE6Pat hRig ggRowE6Pat_EE8 hcfg hX hNP h8).elim
  · exact h6

theorem qtwoDNbr6_rows
    (hRig : GGLabelRigidInput) {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦) {ι : Type}
    {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres 3 (ggAutomizerJoin L Bs 𝒦) M e) (hD : GGIsWeylMatrixD M) {y : G}
    {X : Subgroup G} (hnbr : GGNbr 3 B x D J y X)
    (hA : ggAutomizer X Bs ≤ ggAutomizerJoin L Bs 𝒦) (hns : ¬ GGSplitLie 3 X)
    (hn1 : ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab →
      GGHasLabel lab (↥X ⧸ Subgroup.center ↥X) → lab.n = 1)
    (hrk4 : ∀ hN : Bs ≤ Subgroup.normalizer (X : Set G),
      3 ^ 4 ≤ Nat.card (ggGamma X hN).range)
    (hTw5 : GGInnerDiagOnLabel (fun p lab => ggRowP_ETwE6 p lab ∧ p = 3) 3 Bs X →
      ∀ hN : Bs ≤ Subgroup.normalizer (X : Set G), 3 ^ 5 ≤ Nat.card (ggGamma X hN).range) :
    GGInnerDiagOnLabel (fun p lab =>
      (ggRowP_ESU p lab ∨ ggRowP_EOmP p lab ∨ ggRowP_EOmM p lab) ∧ lab.n = 1) 3 Bs X :=
  qtwoDNbr_rows_of_noF4 hRig hcfg hpres hD hnbr hA hns hn1 (fun hM =>
    ggRow_absurd_of_framePair hcfg hpres (GGIsWeylMatrixAD.le_three (Or.inr hD)) hA
      (ggF4Three_framePair_of_rank hcfg.1.1 hM hrk4)) hTw5

end CFSG.StandardType.QTwo

end
