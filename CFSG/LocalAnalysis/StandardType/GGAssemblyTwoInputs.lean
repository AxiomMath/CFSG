module

public import CFSG.LocalAnalysis.StandardType.GGAssemblyTwoHypSix
public import CFSG.LocalAnalysis.StandardType.GGAssemblyTwoTableB
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwenty
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwo
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoKantorHolds
public import CFSG.LocalAnalysis.StandardType.GGFieldCase
public import CFSG.LocalAnalysis.StandardType.GGFieldNbrTableB
public import CFSG.LocalAnalysis.StandardType.GGInnerDiagBridgeInner
public import CFSG.LocalAnalysis.StandardType.GGNbrBalanceSchreier
public import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerAssembly
public import CFSG.LocalAnalysis.StandardType.GGRootDetectSp
public import CFSG.LocalAnalysis.StandardType.GGRootDetectSpinMinus
public import CFSG.LocalAnalysis.StandardType.GGHypSixAssembly
public import CFSG.LocalAnalysis.StandardType.GGRootInvolutionRest
public import CFSG.LocalAnalysis.StandardType.GGSecFiveTypeA
public import CFSG.LocalAnalysis.StandardType.GGSixOddIndexF4Fixed
public import CFSG.LocalAnalysis.StandardType.GGSixRootCentralizer
public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionLinearSU
public import CFSG.LocalAnalysis.StandardType.GGSixStepOneSchreier
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoprime
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagTwE6

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21

@[expose] def GGFieldNbrSplitInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → GGFieldNbrSplit p Bs x

@[expose] def GGFieldNbrFieldAutInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → GGFieldNbrFieldAut p B Bs x D J

theorem ggBstarNbrNormalInput_of_lBalance (hL : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (ha₀ : GGLNoncyclicInput) : GGBstarNbrNormalInput := by
  intro G _ _ p B Bs x L D J hcfg y K hnbr
  obtain ⟨hI, hBs, hDJ⟩ := hcfg
  have hBsC : Bs ≤ Subgroup.centralizer (Bs : Set G) := fun b hb =>
    Subgroup.mem_centralizer_iff.mpr fun c hc => mul_comm_of_isElemAbelian hBs.2.1 hc hb
  exact (le_inf (le_normalizer_zpowers_of_le (hBs.1 hI.2.2.2.2.2.2.1.2.1) hBsC)
    (le_normalizer_zpowers_of_le (hBs.1 hnbr.1.2.1) hBsC)).trans
    (normalizer_inf_normalizer_le_of_ggNbr hL hI hDJ (hP G p B x L D J hI hDJ) (ha₀ G p B x L hI)
      hnbr)

theorem ggSixNbrCentralizerInput_of_lBalance (hL : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (ha₀ : GGLNoncyclicInput) : GGSixNbrCentralizerInput := by
  intro G _ _ p B x L D J hI hDJ g hg y K hnbr
  have hyD : y ∈ D := by
    rw [hnbr.2.1]
    exact Subgroup.subset_closure (by simp)
  exact normalizer_inf_normalizer_le_of_ggNbr hL hI hDJ (hP G p B x L D J hI hDJ)
    (ha₀ G p B x L hI) hnbr
    ⟨le_normalizer_zpowers_of_le hDJ.1.2.2.2.1 le_rfl hg, le_normalizer_zpowers_of_le hyD le_rfl hg⟩

section StepTwo

theorem ggStepTwoLemmaSixThirteenInput_of_stepOne (h610 : GGSixBstarUniqueV2Input)
    (h611 : GGSixLSixElevenInput) (h613t : GGSixTrialityInput) :
    GGStepTwoLemmaSixThirteenInput := by
  intro G _ _ p B Bs x L D J t n f ψ hctx s1 hlin b hb hC g hg
  by_contra hgM
  have hZ := s1.1
  have hU := h610 G p B Bs x L D J t n f ψ hctx hZ
  rcases h611 G p B Bs x L D J t n f ψ hctx hZ hU b hb hC g hg hgM with hl | ht
  · exact hlin hl.2.2
  · exact hgM (h613t G p B Bs x L D J t n f ψ hctx hZ hU
      (fun d hd hd1 => s1.2.1.centralizer_le hd hd1) b hb hC g hg ht)

end StepTwo

end CFSG.StandardType
