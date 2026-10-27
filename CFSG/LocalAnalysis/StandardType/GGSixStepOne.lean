module

public import CFSG.LocalAnalysis.StandardType.GGSixStepOneNine

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21

section Sylow

variable {G : Type} [Group G]

theorem exists_sylow_of_bstarUnique {p : ℕ} (hp : p.Prime) {M Bs : Subgroup G}
    (hBs : IsElemAbelian p Bs) (hBsM : Bs ≤ M)
    (hU : ∀ P : Subgroup G, P ≤ M → IsPGroup p P → Bs ≤ P →
      (∀ Q : Subgroup G, Q ≤ M → IsPGroup p Q → P ≤ Q → Q = P) →
      ∀ E : Subgroup G, E ≤ P → IsElemAbelian p E →
        Nat.card E ≤ Nat.card Bs ∧ (Nat.card E = Nat.card Bs → E = Bs)) :
    ∃ P : Sylow p M, Bs ≤ (P : Subgroup M).map M.subtype ∧
      ∀ E : Subgroup G, E ≤ (P : Subgroup M).map M.subtype → IsElemAbelian p E →
        Nat.card E = Nat.card Bs → E = Bs := by
  have : Fact p.Prime := ⟨hp⟩
  have hBsp : IsPGroup p Bs := fun b => ⟨1, Subtype.ext (by simpa using hBs.2 b b.2)⟩
  obtain ⟨Q, hQ⟩ := (hBsp.comap_of_injective M.subtype M.subtype_injective).exists_le_sylow
  have hPM : (Q : Subgroup ↥M).map M.subtype ≤ M := Subgroup.map_subtype_le _
  have hPp : IsPGroup p ((Q : Subgroup ↥M).map M.subtype) := Q.isPGroup'.map M.subtype
  have hBsP : Bs ≤ (Q : Subgroup ↥M).map M.subtype := fun b hb => ⟨⟨b, hBsM hb⟩, hQ hb, rfl⟩
  have hmaxM : ∀ R : Subgroup G, R ≤ M → IsPGroup p R →
      (Q : Subgroup ↥M).map M.subtype ≤ R → R = (Q : Subgroup ↥M).map M.subtype := by
    intro R hRM hRp hPR
    have hRp' : IsPGroup p (R.subgroupOf M) :=
      hRp.comap_of_injective M.subtype M.subtype_injective
    have hQR : (Q : Subgroup ↥M) ≤ R.subgroupOf M := fun q hq => hPR ⟨q, hq, rfl⟩
    have hRQ := Q.is_maximal' hRp' hQR
    rw [← Subgroup.map_subgroupOf_eq_of_le hRM, hRQ]
  exact ⟨Q, hBsP, fun E hE hEel hcard => (hU _ hPM hPp hBsP hmaxM E hE hEel).2 hcard⟩

end Sylow

theorem ggSixNeighborNormalInput_of_nbrCentralizer (hnbr : GGSixNbrCentralizerInput)
    (ha₀ : GGLNoncyclicInput) : GGSixNeighborNormalInput := by
  intro G _ _ p B Bs x L D J hctx g hg
  obtain ⟨hs, hnonab, hK, hchar, he, hp, hS, hst, hsix⟩ := hctx
  have hI : GGThmIHyp p B x L := ⟨hs, hnonab, hK, hchar, he, hp, hS, hst⟩
  have hgx : g ∈ Subgroup.centralizer ({x} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hsix.2.1.1.2.2.2.1) hg
  exact ⟨mem_normalizer_of_sstar hS (ha₀ G p B x L hI) hgx,
    fun y K hK' => hnbr G p B x L D J hI hsix.2.1 g hg y K hK'⟩

section Inputs

theorem ggSixBstarUniqueV2Input_of_sylowUnique (h : GGBstarSylowUniqueInput)
    (hR1 : GGLieModelMarkingInput) (hR : GGInnerDiagBridgeInput) : GGSixBstarUniqueV2Input := by
  intro G _ _ p B Bs x L D J t n f ψ hctx _ P hPM hPp hBsP hmax E hE hEel
  exact h G p B Bs x L D J hctx.1 (ggSixHypPre_of_v2Core hR1 hR hctx.2) P hPM hPp hBsP hmax E
    hE hEel

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
  {t : StatedLieTag} {n f : ℕ} {ψ : (ggU t n f).K →* G}

theorem GGSixCtxV2.mem_of_conj_mem_d (h611 : GGSixLSixElevenInput) (h612 : GGSixLSixTwelveInput)
    (h613t : GGSixTrialityInput) (h613d : GGSixLinearJInput)
    (hctx : GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ)
    (hC : Subgroup.centralizer (ggG0 p B x L D J : Set G) = ⊥)
    (hU : GGSixBstarUnique p B Bs x L D J)
    (h9iii : ∀ d ∈ D, d ≠ 1 → Subgroup.centralizer {d} ≤ ggM p B x L D J) {d : G} (hd : d ∈ D)
    (hd1 : d ≠ 1) {g : G} (hg : g⁻¹ * d * g ∈ ggM p B x L D J) : g ∈ ggM p B x L D J := by
  by_contra hgM
  have hdBs : d ∈ Bs := hctx.d_le_bstar hd
  rcases h611 G p B Bs x L D J t n f ψ hctx hC hU d hdBs (h9iii d hd hd1) g hg hgM with
    hlin | htri
  · obtain ⟨hcard, hno⟩ :=
      h612 G p B Bs x L D J t n f ψ hctx hC hU d hdBs (h9iii d hd hd1) g hg hgM hlin
    obtain ⟨K, hK, hKA⟩ := h613d G p B Bs x L D J t n f ψ hctx hlin hcard d hd hd1
    exact hno K hK hKA
  · exact hgM (h613t G p B Bs x L D J t n f ψ hctx hC hU h9iii d hdBs (h9iii d hd hd1) g hg htri)

theorem ggSixStepOneV2Input_of_lemmas (ha₀ : GGLNoncyclicInput) (hc₀ : GGFieldNbrCanonicalInput)
    (hc₁ : GGProp41Input) (hc₂ : GGCor42Input) (hc₃ : GGNoTransvectionInput)
    (hnbr : GGSixNbrCentralizerInput) (h63 : GGSixCentralizerOddInput)
    (h64 : GGSixCentreOddInput) (h65 : GGSixKdComponentInput) (h66 : GGSixCentralizerJInput)
    (h68 : GGSixComponentsNormalInput) (h68i : GGSixInnerOnKdInput)
    (h69 : GGSixInndiagNormalInput) (hS : GGSchreierPerfectInput) (hT : GGTwoSignalizerGenInput)
    (h610 : GGSixBstarUniqueV2Input) (h611 : GGSixLSixElevenInput)
    (h612 : GGSixLSixTwelveInput) (h613t : GGSixTrialityInput) (h613d : GGSixLinearJInput) :
    GGSixStepOneV2Input := by
  intro G _ _ p B Bs x L D J t n f ψ hctx
  have hp := hctx.prime
  have hC2 : Subgroup.centralizer (D : Set G) ≤ ggM p B x L D J :=
    centralizer_le_ggM_of_nbr hctx.sstar (ha₀ G p B x L hctx.thmI) hctx.stdSub.1
      (hnbr G p B x L D J hctx.thmI hctx.stdSub)
  have hodd := h63 G p B Bs x L D J t n f ψ hctx
    (not_dvd_card_centralizer_ggG0_of_stdSub hp hctx.sstar hctx.stdType hctx.stdSub)
  obtain ⟨hZJ, hZK⟩ := h64 G p B Bs x L D J t n f ψ hctx hodd
  have hcomp := h65 G p B Bs x L D J t n f ψ hctx hodd hZJ hZK
  have hCJ := h66 G p B Bs x L D J t n f ψ hctx hC2 hodd hcomp
  have hnorm := h68 G p B Bs x L D J t n f ψ hctx hC2 hodd hcomp
  have hsig := hctx.signalizer_le hC2 hcomp hCJ hnorm
    (h68i G p B Bs x L D J t n f ψ hctx hcomp hCJ hnorm)
  have h9i : ∀ g : G, J.map (MulAut.conj g).toMonoidHom ≤ ggM p B x L D J →
      D.map (MulAut.conj g).toMonoidHom ≤ ggM p B x L D J → g ∈ ggM p B x L D J :=
    fun g hJg hDg => hctx.mem_of_conj_le hS hT hodd hsig hJg hDg
  have h9ii : ∀ d ∈ D, d ≠ 1 →
      Subgroup.normalizer (ggKd p B x L D J d : Set G) ≤ ggM p B x L D J :=
    fun d hd hd1 => hctx.normalizer_ggKd_le h9i hCJ hd
      (h69 G p B Bs x L D J t n f ψ hctx hcomp hCJ d hd hd1)
  have h9iii : ∀ d ∈ D, d ≠ 1 → Subgroup.centralizer {d} ≤ ggM p B x L D J :=
    fun d hd hd1 => hctx.centralizer_le_ggM h9i hd (hcomp d hd hd1) (hnorm d hd hd1)
      (h9ii d hd hd1)
  have hC : Subgroup.centralizer (ggG0 p B x L D J : Set G) = ⊥ :=
    centralizer_eq_bot_of_signalizers hctx.charTwo hp hctx.ne_two hctx.le_ggG0
      hctx.le_centralizer_J hodd hsig hctx.two_dvd_card_j
  have hU := h610 G p B Bs x L D J t n f ψ hctx hC
  have hcfg := hctx.config
  have hOp := hc₁ G p B Bs x L D J hcfg (hc₀ G p B Bs x L D J hcfg)
  have hNoTr := hc₃ G p B Bs x L D J hcfg hOp (hc₂ G p B Bs x L D J hcfg hOp)
  refine ⟨hC, ?_, hsig, exists_sylow_of_bstarUnique hp hctx.bstar.2.1 hctx.bstar_le_normalizer hU,
    not_ggTransvection_of_noTransvection hp hctx.bstar.2.1 hNoTr⟩
  rw [ggControlsStrongFusion_iff]
  exact ⟨hctx.d_le_ggM, fun e he he1 g hg =>
    hctx.mem_of_conj_mem_d h611 h612 h613t h613d hC hU h9iii he he1 hg⟩

end Inputs

section Assembly

theorem lc_gl_std_of_v2_steps_stepOne (hHolt : HoltUniqueFixedPointSimple) (ha : GGBstarInput)
    (ha₀ : GGLNoncyclicInput) (hb : GGStdSubPreInput) (hc₀ : GGFieldNbrCanonicalInput)
    (hc₁ : GGProp41Input) (hc₂ : GGCor42Input) (hc₃ : GGNoTransvectionInput)
    (hd : GGCoxeterLabelInput) (he : GGPropFiveTwentyOneV2Input) (hf : GGHypSixV2Input)
    (hg₁ : GGCorFiveTwentyInput) (hg₂ : GGOmegaOneInput) (hR1 : GGLieModelMarkingInput)
    (hR : GGInnerDiagBridgeInput)
    (hnbr : GGSixNbrCentralizerInput) (h63 : GGSixCentralizerOddInput)
    (h64 : GGSixCentreOddInput) (h65 : GGSixKdComponentInput) (h66 : GGSixCentralizerJInput)
    (h68 : GGSixComponentsNormalInput) (h68i : GGSixInnerOnKdInput)
    (h69 : GGSixInndiagNormalInput) (hS : GGSchreierPerfectInput) (hT : GGTwoSignalizerGenInput)
    (h610 : GGSixBstarUniqueV2Input) (h611 : GGSixLSixElevenInput)
    (h612 : GGSixLSixTwelveInput) (h613t : GGSixTrialityInput) (h613d : GGSixLinearJInput)
    (h2 : GGSixStepTwoV2Input) (h3a : GGSixStepThreeAInput) (h3b : GGSixStepThreeBInput)
    (h3c : GGSixStepThreeCInput) (h3d : GGSixStepThreeDInput)
    (hKG : GGRootInvolutionCentralInput)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hK : KProper InCatalog G) (hchar : IsCharTwoType G)
    (he4 : 4 ≤ evenRank G) (p : ℕ) (hp : p ∈ LargeEvenBeta 4 G) (B : Subgroup G) (x : G)
    (L : Subgroup G) (hS' : LargeEvenSStar p B x L) (hst : LargeEvenStandardType p B x L) :
    InCatalog G :=
  lc_gl_std_of_v2_steps' hHolt ha ha₀ hb hc₀ hc₁ hc₂ hc₃ hd he hf hg₁ hg₂ hR1 hR
    (ggSixStepOneV2Input_of_lemmas ha₀ hc₀ hc₁ hc₂ hc₃ hnbr h63 h64 h65 h66 h68 h68i h69 hS hT
      h610 h611 h612 h613t h613d) h2 h3a h3b h3c h3d hKG G hnonab hK hchar he4 p hp B x L hS' hst

end Assembly

end CFSG.StandardType
