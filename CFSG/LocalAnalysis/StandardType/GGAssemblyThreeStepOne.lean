module

public import CFSG.LocalAnalysis.StandardType.GGSixLSixElevenWire
public import CFSG.LocalAnalysis.StandardType.GGSixStepOneOutdiagStep

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

section Inputs

theorem ggSixTwoLocalRankInput_of_lemmas_d (ha₀ : GGLNoncyclicInput)
    (hnbr : GGSixNbrCentralizerInput) (h63 : GGSixCentralizerOddInput)
    (h64 : GGSixCentreOddInput) (h65 : GGSixKdComponentInput) (h66 : GGSixCentralizerJInput)
    (h68 : GGSixComponentsNormalInput) (h68i : GGSixInnerOnKdInput)
    (h69 : GGSixInndiagNormalDInput) (hS : GGSchreierPerfectInput)
    (hT : GGTwoSignalizerGenInput) : GGSixTwoLocalRankInput := by
  intro G _ _ p B Bs x L D J t n f ψ hctx _ _
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
  have h9iii : ∀ d ∈ D, d ≠ 1 → Subgroup.centralizer {d} ≤ ggM p B x L D J :=
    fun d hd hd1 => hctx.centralizer_le_ggM h9i hd (hcomp d hd hd1) (hnorm d hd hd1)
      (h9ii d hd hd1)
  exact hctx.twoLocalRankFour h9iii

theorem ggSixLSixElevenInput_of_lemmas_d (hKG : GGSixLSixElevenKGInput)
    (ha₀ : GGLNoncyclicInput) (hnbr : GGSixNbrCentralizerInput)
    (h63 : GGSixCentralizerOddInput) (h64 : GGSixCentreOddInput) (h65 : GGSixKdComponentInput)
    (h66 : GGSixCentralizerJInput) (h68 : GGSixComponentsNormalInput)
    (h68i : GGSixInnerOnKdInput) (h69 : GGSixInndiagNormalDInput) (hS : GGSchreierPerfectInput)
    (hT : GGTwoSignalizerGenInput) : GGSixLSixElevenInput :=
  ggSixLSixElevenInput_of_kg hKG
    (ggSixTwoLocalRankInput_of_lemmas_d ha₀ hnbr h63 h64 h65 h66 h68 h68i h69 hS hT)

end Inputs

end CFSG.StandardType
