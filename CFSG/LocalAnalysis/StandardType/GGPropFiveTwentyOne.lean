module

public import CFSG.LocalAnalysis.StandardType.GGPropFiveTwentyOneCent

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21

section Input

@[expose] def GGSecFiveDataInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → GGOpAutTrivial p Bs → GGInnerDiagAll p B Bs x L D J →
      GGNoTransvection p Bs →
      (∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K → GGReflGenerated p (ggAutomizer K Bs) →
        GGScalarsOrWeyl' p B Bs x D J →
          GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs)) →
      (∃ m k f : ℕ, 4 ≤ k ∧ k ≤ m ∧ 1 ≤ f ∧ GGSecFiveTypeA p B x L D J m k f) ∨
      (∃ (t : StatedLieTag) (n f : ℕ), GGSecFiveLocal p B x L D J t n f) ∨
      (∃ (t : StatedLieTag) (n f : ℕ), GGSecFivePres p B x L D J t n f)

end Input

section Wiring

theorem ggPropFiveTwentyOneV2Input_of_data (h : GGSecFiveDataInput) :
    GGPropFiveTwentyOneV2Input := by
  intro G _ _ p B Bs x L D J hcfg hOp hInn hNoTr hW
  rcases h G p B Bs x L D J hcfg hOp hInn hNoTr hW with ⟨m, k, f, hk, hkm, hf, hA⟩ |
    ⟨t, n, f, hloc⟩ | ⟨t, n, f, hpres⟩
  · obtain ⟨ψ, hψ⟩ := ggPresentsG0_of_typeA hk hkm hf hA
    exact ⟨.PSL, m + 1, f, ψ, hψ⟩
  · obtain ⟨ψ, hψ⟩ := ggPresentsG0_of_secFivePres (ggSecFivePres_of_local hloc)
    exact ⟨t, n, f, ψ, hψ⟩
  · obtain ⟨ψ, hψ⟩ := ggPresentsG0_of_secFivePres hpres
    exact ⟨t, n, f, ψ, hψ⟩

end Wiring

section Assembly

theorem lc_gl_std_of_secFiveData (hHolt : HoltUniqueFixedPointSimple) (ha : GGBstarInput)
    (ha₀ : GGLNoncyclicInput) (hb : GGStdSubPreInput) (hc₀ : GGFieldNbrCanonicalInput)
    (hc₁ : GGProp41Input) (hc₂ : GGCor42Input) (hc₃ : GGNoTransvectionInput)
    (hd : GGCoxeterLabelInput) (he : GGSecFiveDataInput) (hf : GGHypSixV2Input)
    (hg₁ : GGCorFiveTwentyInput) (hg₂ : GGOmegaOneInput) (hR1 : GGLieModelMarkingInput)
    (hR : GGInnerDiagBridgeInput) (h1 : GGSixStepOneV2Input) (h2 : GGSixStepTwoV2Input)
    (h3a : GGSixStepThreeAInput) (h3b : GGSixStepThreeBInput) (h3c : GGSixStepThreeCInput)
    (h3d : GGSixStepThreeDInput) (hKG : GGRootInvolutionCentralInput)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hK : KProper InCatalog G) (hchar : IsCharTwoType G)
    (he4 : 4 ≤ evenRank G) (p : ℕ) (hp : p ∈ LargeEvenBeta 4 G) (B : Subgroup G) (x : G)
    (L : Subgroup G) (hS : LargeEvenSStar p B x L) (hst : LargeEvenStandardType p B x L) :
    InCatalog G :=
  lc_gl_std_of_v2_steps' hHolt ha ha₀ hb hc₀ hc₁ hc₂ hc₃ hd
    (ggPropFiveTwentyOneV2Input_of_data he) hf hg₁ hg₂ hR1 hR h1 h2 h3a h3b h3c h3d hKG
    G hnonab hK hchar he4 p hp B x L hS hst

end Assembly

end CFSG.StandardType
