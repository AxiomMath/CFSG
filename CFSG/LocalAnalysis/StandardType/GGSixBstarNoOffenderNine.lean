module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderExc
public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderClassicalDefs
public import CFSG.LocalAnalysis.StandardType.GGSixStepOneOutdiagStep

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

section Nine

@[expose] def GGSixNineIIIInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ →
    ∀ d ∈ D, d ≠ 1 → Subgroup.centralizer {d} ≤ ggM p B x L D J

theorem ggSixNineIIIInput_of_lemmas_d (ha₀ : GGLNoncyclicInput)
    (hnbr : GGSixNbrCentralizerInput) (h63 : GGSixCentralizerOddInput)
    (h64 : GGSixCentreOddInput) (h65 : GGSixKdComponentInput)
    (h66 : GGSixCentralizerJInput) (h68 : GGSixComponentsNormalInput)
    (h68i : GGSixInnerOnKdInput) (h69 : GGSixInndiagNormalDInput)
    (hS : GGSchreierPerfectInput) (hT : GGTwoSignalizerGenInput) : GGSixNineIIIInput := by
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
    fun d hd hd1 => hctx.normalizer_ggKd_le_of_d h9i hCJ hd
      (h69 G p B Bs x L D J t n f ψ hctx hcomp hCJ d hd hd1)
  exact fun d hd hd1 => hctx.centralizer_le_ggM h9i hd (hcomp d hd hd1) (hnorm d hd hd1)
    (h9ii d hd hd1)

@[expose] def GGSixBstarNoOffenderNineOn (P : StatedLieTag → ℕ → ℕ → ℕ → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G), P t n f p →
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ →
    Subgroup.centralizer (ggG0 p B x L D J : Set G) = ⊥ →
    (∀ d ∈ D, d ≠ 1 → Subgroup.centralizer {d} ≤ ggM p B x L D J) →
    GGNoOffender p (ggM p B x L D J) Bs

theorem ggSixBstarNoOffenderOn_of_nineOn {P : StatedLieTag → ℕ → ℕ → ℕ → Prop}
    (h : GGSixBstarNoOffenderNineOn P) (h9 : GGSixNineIIIInput) : GGSixBstarNoOffenderOn P :=
  fun G _ _ p B Bs x L D J t n f ψ hP hctx hC =>
    h G p B Bs x L D J t n f ψ hP hctx hC (h9 G p B Bs x L D J t n f ψ hctx)

@[expose] def GGSixBstarNoOffenderExcRestNine : Prop :=
  GGSixBstarNoOffenderOn GGExcE6ThreeLabel ∧ GGSixBstarNoOffenderNineOn GGExcTwE6ThreeLabel ∧
    GGSixBstarNoOffenderOn GGExcE8QuarticFiveLabel

theorem ggSixBstarNoOffenderExcRest_of_nine (h : GGSixBstarNoOffenderExcRestNine)
    (h9 : GGSixNineIIIInput) : GGSixBstarNoOffenderExcRest :=
  ⟨h.1, ggSixBstarNoOffenderOn_of_nineOn h.2.1 h9, h.2.2⟩

end Nine

section Outdiag

theorem ggSixNineIIIInput_of_lemmas_outdiag (ha₀ : GGLNoncyclicInput)
    (hc₀ : GGFieldNbrCanonicalInput) (hc₁ : GGProp41Input) (hc₂ : GGCor42Input)
    (hnbr : GGSixNbrCentralizerInput) (h63 : GGSixCentralizerOddInput)
    (h64 : GGSixCentreOddInput) (h65 : GGSixKdComponentInput)
    (h66 : GGSixCentralizerJInput) (h68 : GGSixComponentsNormalInput)
    (hN : GGInndiagNormalInput) (hpJ : GGStdSubPrimeInput) (hS : GGSchreierPerfectInput)
    (hT : GGTwoSignalizerGenInput) : GGSixNineIIIInput :=
  ggSixNineIIIInput_of_lemmas_d ha₀ hnbr h63 h64 h65 h66 h68
    (ggSixInnerOnKdInput_of_prime hN hc₀ hc₁ hc₂ hpJ)
    (ggSixInndiagNormalDInput_of_prime hN hc₀ hc₁ hc₂ hpJ) hS hT

end Outdiag

end CFSG.StandardType
