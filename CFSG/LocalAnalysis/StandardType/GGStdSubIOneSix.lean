module

public import CFSG.LocalAnalysis.StandardType.GGStdSubIOneExist
public import CFSG.LocalAnalysis.StandardType.GGKGroupFusionBridge
public import CFSG.LocalAnalysis.StandardType.GGLinearFusionSUComp
public import CFSG.LocalAnalysis.StandardType.GGInnerDiagBridgeSUDiag
public import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerMinus

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21

section Inputs

@[expose] def GGSixStepTwoV2I1Input : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ →
    Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D → GGSixStepOne p B Bs x L D J →
      GGSixStepTwo p B Bs x L D J

theorem ggSixStepTwoV2I1Input_of_inputs (h613 : GGStepTwoLemmaSixThirteenInput)
    (hA : GGStepTwoLinearFusionEqInput) (h614 : GGStepTwoSubnormalInput)
    (h615 : GGStepTwoCentralizerInput) : GGSixStepTwoV2I1Input := by
  intro G _ _ p B Bs x L D J t n f ψ hctx hI1 s1 b hb hb1 L₁ hcomp hcard
  have hpair : GGStepTwoPair p B Bs x L D J b L₁ := ⟨hb, hb1, hcomp, hcard⟩
  have hp : p.Prime := hctx.1.2.2.2.2.2.1.1
  obtain ⟨⟨-, hBs, -⟩, -, -, -, -, ⟨hBsM, -⟩, -, hNBs⟩ := hctx.2
  by_cases hlin : GGStepTwoLinearType p t f
  · obtain ⟨m, hm, hmD⟩ := hA G p B Bs x L D J t n f ψ hctx s1 hlin hI1 b L₁ hpair
    exact hpair.stepTwo_of_conj_mem s1.2.1 (hNBs hm) hmD
  · have hsn := h614 G p B Bs x L D J t n f ψ hctx s1 hlin b L₁ hpair
    have hC : Subgroup.centralizer {b} ≤ ggM p B x L D J := by
      rcases (D ⊓ (Subgroup.zpowers b ⊔ L₁)).bot_or_exists_ne_one with hDR | ⟨d, hd, hd1⟩
      · exact h615 G p B Bs x L D J t n f ψ hctx s1 hlin b L₁ hpair hsn hDR
      · exact hpair.centralizer_le_of_mem hBsM s1.2.1 hsn (Subgroup.mem_inf.mp hd).1 hd1
          (Subgroup.mem_inf.mp hd).2
    exact hpair.stepTwo_of_fusion hp hBs hBsM hC
      (h613 G p B Bs x L D J t n f ψ hctx s1 hlin b hb hC)

theorem ggSecSixV2I1Input_of_inputs (h1 : GGSixStepOneV2Input) (h2 : GGSixStepTwoV2I1Input)
    (h3a : GGSixStepThreeAInput) (h3b : GGSixStepThreeBInput) (h3c : GGSixStepThreeCInput)
    (h3d : GGSixStepThreeDInput) (hKG : GGRootInvolutionCentralInput) : GGSecSixV2I1Input := by
  intro G _ _ _ hnonab hK hchar he p hp B x L hS hst Bs D J t n f ψ hsix hI1
  have hctx : GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ :=
    ⟨⟨inferInstance, hnonab, hK, hchar, he, hp, hS, hst⟩, hsix⟩
  have s1 := h1 G p B Bs x L D J t n f ψ hctx
  exact ggSix_holt_of_stepThree (ggSixStepThree_of_split h3a h3b h3c h3d hKG hctx s1
    (h2 G p B Bs x L D J t n f ψ hctx hI1 s1))

end Inputs

section Assembly

theorem ggInnerDiagMarkingInput_of_E6
    (hR : ∀ t, (t = .E6 ∨ t = .twistedE6) → GGInnerDiagMarkingAt t) :
    GGInnerDiagMarkingInput := by
  have hI : ∀ t, GGInnerTag t → GGInnerDiagMarkingAt t := fun t ht =>
    ggInnerDiagMarkingAt_of_diagInner ht (ggPsiDiagInnerAt_of_ggInnerTag t ht)
  refine ggInnerDiagMarkingInput_of_open ggInnerDiagMarkingAt_PSL fun t ht => ?_
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ggInnerDiagMarkingAt_PSU
  · exact hI _ (.inl rfl)
  · exact hI _ (.inr (.inl rfl))
  · exact hI _ (.inr (.inr (.inl rfl)))
  · exact hI _ (.inr (.inr (.inr (.inl rfl))))
  · exact hR _ (.inl rfl)
  · exact hI _ (.inr (.inr (.inr (.inr (.inl rfl)))))
  · exact hI _ (.inr (.inr (.inr (.inr (.inr rfl)))))
  · exact hR _ (.inr rfl)

end Assembly

end CFSG.StandardType
