module

public import CFSG.LocalAnalysis.StandardType.GGHypSixTypeA
public import CFSG.LocalAnalysis.StandardType.GGReverseMarkingAssembly

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21

section Families

theorem ggRootDetect_of_rank_lt {t : StatedLieTag} (h : ∀ n f, (ggU t n f).D.rank < 2) :
    GGRootDetect t := by
  intro G _ _ n f ψ _ hrk
  exact absurd hrk (Nat.not_le.mpr (h n f))

theorem ggRootDetect_pOmegaOdd : GGRootDetect .POmegaOdd := by
  intro G _ _ n f ψ hadm
  exact absurd rfl hadm.2.2.2

@[expose] def GGRootDetectRest : Prop :=
  GGRootDetect .PSU ∧ GGRootDetect .PSp ∧ GGRootDetect .POmegaPlus ∧
    GGRootDetect .POmegaMinus ∧ GGRootDetect .F4 ∧ GGRootDetect .E6 ∧ GGRootDetect .E7 ∧
    GGRootDetect .E8 ∧ GGRootDetect .twistedE6

theorem ggRootDetect_all (h : GGRootDetectRest) : ∀ t, GGRootDetect t := by
  obtain ⟨hU, hSp, hP, hM, hF4, hE6, hE7, hE8, h2E6⟩ := h
  intro t
  cases t
  · exact ggRootDetect_psl
  · exact hU
  · exact hSp
  · exact ggRootDetect_pOmegaOdd
  · exact hP
  · exact hM
  · exact ggRootDetect_of_rank_lt fun _ _ => Nat.zero_lt_two
  · exact hF4
  · exact hE6
  · exact hE7
  · exact hE8
  · exact h2E6
  · exact ggRootDetect_of_rank_lt fun _ _ => Nat.zero_lt_two
  · exact ggRootDetect_of_rank_lt fun _ _ => Nat.zero_lt_two
  · exact ggRootDetect_of_rank_lt fun _ _ => Nat.zero_lt_two
  · exact ggRootDetect_of_rank_lt fun _ _ => Nat.zero_lt_two
  · exact ggRootDetect_of_rank_lt fun _ _ => Nat.zero_lt_two

theorem ggHypSixV2Input_of_rest (hR : GGInnerDiagBridgeInput) (hC : GGCompatNbrInput)
    (hrest : GGRootDetectRest) (hD4 : GGHypSixD4Input) : GGHypSixV2Input :=
  ggHypSixV2Input_of_detect hR hC (ggRootDetect_all hrest) hD4

end Families

section Assembly

theorem lc_gl_std_of_v2_steps_six (hHolt : HoltUniqueFixedPointSimple) (ha : GGBstarInput)
    (ha₀ : GGLNoncyclicInput) (hb : GGStdSubPreInput) (hc₀ : GGFieldNbrCanonicalInput)
    (hc₁ : GGProp41Input) (hc₂ : GGCor42Input) (hc₃ : GGNoTransvectionInput)
    (hd : GGCoxeterLabelInput) (he : GGPropFiveTwentyOneV2Input) (hC : GGCompatNbrInput)
    (hrest : GGRootDetectRest) (hD4 : GGHypSixD4Input)
    (hg₁ : GGCorFiveTwentyInput) (hg₂ : GGOmegaOneInput) (hR : GGInnerDiagBridgeInput)
    (h1 : GGSixStepOneV2Input) (h2 : GGSixStepTwoV2Input) (h3a : GGSixStepThreeAInput)
    (h3b : GGSixStepThreeBInput) (h3c : GGSixStepThreeCInput) (h3d : GGSixStepThreeDInput)
    (hKG : GGRootInvolutionCentralInput)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hK : KProper InCatalog G) (hchar : IsCharTwoType G)
    (he4 : 4 ≤ evenRank G) (p : ℕ) (hp : p ∈ LargeEvenBeta 4 G) (B : Subgroup G) (x : G)
    (L : Subgroup G) (hS : LargeEvenSStar p B x L) (hst : LargeEvenStandardType p B x L) :
    InCatalog G :=
  lc_gl_std_of_v2_steps_rev hHolt ha ha₀ hb hc₀ hc₁ hc₂ hc₃ hd he
    (ggHypSixV2Input_of_rest hR hC hrest hD4) hg₁ hg₂ hR h1 h2 h3a h3b h3c h3d hKG G hnonab hK
    hchar he4 p hp B x L hS hst

end Assembly

end CFSG.StandardType
