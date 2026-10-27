module

public import CFSG.LocalAnalysis.StandardType.GGReverseMarking
public import CFSG.LocalAnalysis.StandardType.GGInterfaceFive

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21

section Presented

theorem largeEvenMarking_of_ggPresentsG0 {G : Type} [Group G] {U : Type} [Group U]
    {G₀ : Subgroup G} {Δ : UniversalRootDatum U} {t : StatedLieTag} {n f : ℕ} {ψ : U →* G}
    (h : GGPresentsG0 G₀ Δ t n f ψ) :
    LargeEvenMarking ↥G₀ fun lab _ _ _ _ _ =>
      markTag lab = t ∧ markRank lab = n ∧ markChar lab = 2 ∧ markDeg lab = f :=
  largeEvenMarking_of_lieModel_centerQuot h.2.2.1 h.2.2.2

end Presented

section Assembly

theorem lc_gl_std_of_v2_steps_rev (hHolt : HoltUniqueFixedPointSimple) (ha : GGBstarInput)
    (ha₀ : GGLNoncyclicInput) (hb : GGStdSubPreInput) (hc₀ : GGFieldNbrCanonicalInput)
    (hc₁ : GGProp41Input) (hc₂ : GGCor42Input) (hc₃ : GGNoTransvectionInput)
    (hd : GGCoxeterLabelInput) (he : GGPropFiveTwentyOneV2Input) (hf : GGHypSixV2Input)
    (hg₁ : GGCorFiveTwentyInput) (hg₂ : GGOmegaOneInput) (hR : GGInnerDiagBridgeInput)
    (h1 : GGSixStepOneV2Input) (h2 : GGSixStepTwoV2Input) (h3a : GGSixStepThreeAInput)
    (h3b : GGSixStepThreeBInput) (h3c : GGSixStepThreeCInput) (h3d : GGSixStepThreeDInput)
    (hKG : GGRootInvolutionCentralInput)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hK : KProper InCatalog G) (hchar : IsCharTwoType G)
    (he4 : 4 ≤ evenRank G) (p : ℕ) (hp : p ∈ LargeEvenBeta 4 G) (B : Subgroup G) (x : G)
    (L : Subgroup G) (hS : LargeEvenSStar p B x L) (hst : LargeEvenStandardType p B x L) :
    InCatalog G :=
  lc_gl_std_of_v2_steps' hHolt ha ha₀ hb hc₀ hc₁ hc₂ hc₃ hd he hf hg₁ hg₂
    ggLieModelMarkingInput_holds hR h1 h2 h3a h3b h3c h3d hKG G hnonab hK hchar he4 p hp B x L
    hS hst

end Assembly

end CFSG.StandardType
