module

public import CFSG.LocalAnalysis.StandardType.GGInterfaceSix
public import CFSG.LocalAnalysis.StandardType.GGPresentation
public import CFSG.Milestones.CL_LIT_Curtis_Tits_presentation_theorem
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123
public import CFSG.LieType.CurtisTits

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21

section Core

variable {G : Type} [Group G] {U : Type} [Group U]

@[expose] def GGPresentsG0 (G₀ : Subgroup G) (Δ : UniversalRootDatum U) (t : StatedLieTag)
    (n f : ℕ) (ψ : U →* G) : Prop :=
  (StatedLieAdmissible t n 2 f ∧ 2 ≤ Δ.rank) ∧ (ψ.range = G₀ ∧ ψ.ker ≤ Subgroup.center U) ∧
    commutator ↥G₀ = ⊤ ∧ LieModel (↥G₀ ⧸ Subgroup.center ↥G₀) t n 2 f

end Core

section Inputs

@[expose] def GGPropFiveTwentyOneV2Input : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → GGOpAutTrivial p Bs → GGInnerDiagAll p B Bs x L D J →
      GGNoTransvection p Bs →
      (∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K → GGReflGenerated p (ggAutomizer K Bs) →
        GGScalarsOrWeyl' p B Bs x D J →
          GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs)) →
      ∃ (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
        GGPresentsG0 (ggG0 p B x L D J) (ggU t n f).D t n f ψ

@[expose] def GGHypSixV2Input : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → GGOpAutTrivial p Bs → GGInnerDiagAll p B Bs x L D J →
      ∀ (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
        GGPresentsG0 (ggG0 p B x L D J) (ggU t n f).D t n f ψ →
        Bs ≤ Subgroup.normalizer (ggG0 p B x L D J : Set G) →
          ∀ b ∈ Bs, GGPsiInnerDiag (ggU t n f).D ψ b

variable {G : Type} [Group G] [Finite G]

theorem ggInnerDiagOn_of_presents (hR1 : GGLieModelMarkingInput) (hR : GGInnerDiagBridgeInput)
    {G₀ Bs : Subgroup G} {t : StatedLieTag} {n f : ℕ} {ψ : (ggU t n f).K →* G}
    (hpres : GGPresentsG0 G₀ (ggU t n f).D t n f ψ)
    (hBsN : Bs ≤ Subgroup.normalizer (G₀ : Set G))
    (hVI : ∀ b ∈ Bs, GGPsiInnerDiag (ggU t n f).D ψ b) : GGInnerDiagOn Bs G₀ := by
  obtain ⟨⟨hadm, hrk⟩, ⟨hrange, hker⟩, hperf, hmodel⟩ := hpres
  have hm1 := hR G t n f ψ hadm hrk hker _ hrange _ (hR1 _ t n f hadm hperf hmodel)
  exact largeEvenMarking_mono (fun lab R _ I F θ hP => ⟨hBsN, fun b hb =>
    (hP.2 b (hBsN hb)).mpr (hVI b hb)⟩) hm1

theorem ggPropFiveTwentyOneInput_of_v2 (he : GGPropFiveTwentyOneV2Input)
    (hR1 : GGLieModelMarkingInput) : GGPropFiveTwentyOneInput := by
  intro G _ _ p B Bs x L D J hcfg hOp hInn hNoTr hW
  obtain ⟨t, n, f, ψ, ⟨hadm, -⟩, -, hperf, hmodel⟩ := he G p B Bs x L D J hcfg hOp hInn hNoTr hW
  exact hR1 _ t n f hadm hperf hmodel

theorem ggHypSixV2Input_of_hypSix (hf : GGHypSixInput) (hR1 : GGLieModelMarkingInput)
    (hR : GGInnerDiagBridgeInput) : GGHypSixV2Input := by
  intro G _ _ p B Bs x L D J hcfg hOp hInn t n f ψ hpres hBsN b hb
  obtain ⟨⟨hadm, hrk⟩, ⟨hrange, hker⟩, hperf, hmodel⟩ := hpres
  have hm0 := hR1 _ t n f hadm hperf hmodel
  have hm1 := hR G t n f ψ hadm hrk hker _ hrange _ (hf G p B Bs x L D J hcfg hOp hInn hm0 hBsN)
  obtain ⟨-, lab, -, hraw⟩ := hm1
  obtain ⟨R, _, I, F, -, -, θ, hI, hiff⟩ := largeEvenRawDatum_exists hraw
  exact (hiff b (hBsN hb)).mp (hI b hb)

theorem ggSecOneFiveV2Input_of_inputs (ha : GGBstarInput) (ha₀ : GGLNoncyclicInput)
    (hb : GGStdSubPreInput) (hc₀ : GGFieldNbrCanonicalInput) (hc₁ : GGProp41Input)
    (hc₂ : GGCor42Input) (hc₃ : GGNoTransvectionInput) (hd : GGCoxeterLabelInput)
    (he : GGPropFiveTwentyOneV2Input) (hf : GGHypSixV2Input) (hg₁ : GGCorFiveTwentyInput)
    (hg₂ : GGOmegaOneInput) (hR1 : GGLieModelMarkingInput) (hR : GGInnerDiagBridgeInput) :
    GGSecOneFiveV2Input := by
  intro G _ _ _ hnonab hK hchar he4 p hp B x L hS hst
  have hI : GGThmIHyp p B x L := ⟨inferInstance, hnonab, hK, hchar, he4, hp, hS, hst⟩
  obtain ⟨Bs, hBs⟩ := ha G p B x L hI
  obtain ⟨D, J, hDJ⟩ := exists_stdSub_of_stdSubPre (hb G p B x L hI)
  have hcfg : GGConfig p B Bs x L D J := ⟨hI, hBs, hDJ⟩
  have hOp := hc₁ G p B Bs x L D J hcfg (hc₀ G p B Bs x L D J hcfg)
  have hInn := hc₂ G p B Bs x L D J hcfg hOp
  have hNoTr := hc₃ G p B Bs x L D J hcfg hOp hInn
  have hW := hd G p B Bs x L D J hcfg hOp hInn hNoTr
  obtain ⟨t, n, f, ψ, hpres⟩ := he G p B Bs x L D J hcfg hOp hInn hNoTr hW
  have hnc := ha₀ G p B x L hI
  have hBsN := bstar_le_normalizer_ggG0 hS hnc hDJ.1 hBs
  have hVI := hf G p B Bs x L D J hcfg hOp hInn t n f ψ hpres hBsN
  have hNBs := hg₁ G p B Bs x L D J hcfg hOp hInn hNoTr
    (ggInnerDiagOn_of_presents hR1 hR hpres hBsN hVI)
  have hCB := centralizer_le_normalizer_ggG0 hS hnc hDJ.1
  have hNB := normalizer_le_of_frattini hp.1 hBs (hg₂ G p B Bs x L D J hcfg hOp hInn) hCB hNBs
  obtain ⟨⟨hadm, hrk⟩, ⟨hrange, hker⟩, hperf, hmodel⟩ := hpres
  exact ⟨Bs, D, J, t, n, f, ψ, hBs, hDJ, ⟨hadm, hrk⟩, ⟨hrange, hker⟩, ⟨hperf, hmodel⟩,
    ⟨hBsN, hVI⟩, hNB, hNBs⟩

end Inputs

section Presentation

theorem ggPresentsG0_of_presentation {G : Type} [Group G] (t : StatedLieTag) (n f : ℕ)
    (hadm : StatedLieAdmissible t n 2 f) (hrank : 3 ≤ bnRank t n)
    (hrk : 2 ≤ (ggU t n f).D.rank) {ν : GGWeyl (ggU t n f).D →* (ggU t n f).K}
    (hν : GGWeylLift (ggU t n f).D ν) {ι : Type*} {S : ι → Set (Fin (ggU t n f).D.rank → ℤ)}
    (hS : ∀ k, S k ⊆ (ggU t n f).D.roots) (φ : ∀ k, ggSub (ggU t n f).D (S k) →* G)
    {R : Subgroup G} {δ : R →* GGWeyl (ggU t n f).D} (hδ : Function.Surjective δ)
    (hC : GGActsLike (ggU t n f).D S φ ν R δ) (hW : GGWeylInR (ggU t n f).D S φ ν R δ)
    (horb : GGOrbit (ggU t n f).D S)
    (hnt : ∃ k, ∃ γ ∈ S k, ∃ z ∈ (ggU t n f).D.rootGroup γ, ggExt (φ k) z ≠ 1)
    {G₀ : Subgroup G} (hcl : ggClosure (ggU t n f).D S φ R = G₀) :
    ∃ ψ : (ggU t n f).K →* G, GGPresentsG0 G₀ (ggU t n f).D t n f ψ ∧
      ∀ k (x : ggSub (ggU t n f).D (S k)), ψ x = φ k x := by
  subst hcl
  obtain ⟨ψ, hext, -, -, hrange, hker, hq, hmodel⟩ :=
    ggPresentation (CFSG.Milestones.cl_lit_curtis_tits_presentation_theorem.{0} t n 2 f hadm hrank)
        hν hS φ hδ hC hW horb hnt
  exact ⟨ψ, ⟨⟨hadm, hrk⟩, ⟨hrange, hker⟩, Group.isPerfect_def.mp hq.1, hmodel⟩, hext⟩

end Presentation

section Assembly

theorem lc_gl_std_of_v2_steps (hHolt : HoltUniqueFixedPointSimple) (ha : GGBstarInput)
    (ha₀ : GGLNoncyclicInput) (hb : GGStdSubPreInput) (hc₀ : GGFieldNbrCanonicalInput)
    (hc₁ : GGProp41Input) (hc₂ : GGCor42Input) (hc₃ : GGNoTransvectionInput)
    (hd : GGCoxeterLabelInput) (he : GGPropFiveTwentyOneV2Input) (hf : GGHypSixInput)
    (hg₁ : GGCorFiveTwentyInput) (hg₂ : GGOmegaOneInput) (ha'₁ : GGBstarSylowUniqueInput)
    (hR1 : GGLieModelMarkingInput) (hR : GGInnerDiagBridgeInput) (h1 : GGSixStepOneInput)
    (h2 : GGSixStepTwoInput) (h3a : GGSixStepThreeAInput) (h3b : GGSixStepThreeBInput)
    (h3c : GGSixStepThreeCInput) (h3d : GGSixStepThreeDInput)
    (hKG : GGRootInvolutionCentralInput)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hK : KProper InCatalog G) (hchar : IsCharTwoType G)
    (he4 : 4 ≤ evenRank G) (p : ℕ) (hp : p ∈ LargeEvenBeta 4 G) (B : Subgroup G) (x : G)
    (L : Subgroup G) (hS : LargeEvenSStar p B x L) (hst : LargeEvenStandardType p B x L) :
    InCatalog G :=
  have ha' := ggBstarRankInput_of_sylowUnique ha'₁
  lc_gl_std_of_v2_inputs hHolt
    (ggSecOneFiveV2Input_of_inputs ha ha₀ hb hc₀ hc₁ hc₂ hc₃ hd he
      (ggHypSixV2Input_of_hypSix hf hR1 hR) hg₁ hg₂ hR1 hR)
    (ggSecSixV2Input_of_inputs (ggSixStepOneV2Input_of_input h1 hR1 hR ha')
      (ggSixStepTwoV2Input_of_input h2 hR1 hR ha') h3a h3b h3c h3d hKG)
    G hnonab hK hchar he4 p hp B x L hS hst

theorem lc_gl_std_of_v2_steps' (hHolt : HoltUniqueFixedPointSimple) (ha : GGBstarInput)
    (ha₀ : GGLNoncyclicInput) (hb : GGStdSubPreInput) (hc₀ : GGFieldNbrCanonicalInput)
    (hc₁ : GGProp41Input) (hc₂ : GGCor42Input) (hc₃ : GGNoTransvectionInput)
    (hd : GGCoxeterLabelInput) (he : GGPropFiveTwentyOneV2Input) (hf : GGHypSixV2Input)
    (hg₁ : GGCorFiveTwentyInput) (hg₂ : GGOmegaOneInput) (hR1 : GGLieModelMarkingInput)
    (hR : GGInnerDiagBridgeInput) (h1 : GGSixStepOneV2Input) (h2 : GGSixStepTwoV2Input)
    (h3a : GGSixStepThreeAInput) (h3b : GGSixStepThreeBInput) (h3c : GGSixStepThreeCInput)
    (h3d : GGSixStepThreeDInput) (hKG : GGRootInvolutionCentralInput)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hK : KProper InCatalog G) (hchar : IsCharTwoType G)
    (he4 : 4 ≤ evenRank G) (p : ℕ) (hp : p ∈ LargeEvenBeta 4 G) (B : Subgroup G) (x : G)
    (L : Subgroup G) (hS : LargeEvenSStar p B x L) (hst : LargeEvenStandardType p B x L) :
    InCatalog G :=
  lc_gl_std_of_v2_inputs hHolt
    (ggSecOneFiveV2Input_of_inputs ha ha₀ hb hc₀ hc₁ hc₂ hc₃ hd he hf hg₁ hg₂ hR1 hR)
    (ggSecSixV2Input_of_inputs h1 h2 h3a h3b h3c h3d hKG)
    G hnonab hK hchar he4 p hp B x L hS hst

end Assembly

end CFSG.StandardType
