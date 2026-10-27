module

public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenSixSym
public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenSixQ16
import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenSixSPhiProof

public section

namespace CFSG.RankThree.PartTwo.Sec19.SolEven

open CFSG CFSG.QuasithinUnique CFSG.RankThree.PartTwo
open CFSG.OddStandard.HigherRank.YamadaG23 (StrothSigma6 FooteMainL6)
open CFSG.ComponentClassification.StandardRecognition (ClassicalInvolutionTheoremModels)
open CFSG.GF2Type.Smith1979W3 (Smith1979WidthThreeCharTwoKP)

theorem evenN_six_of_branches
    (hNode : CFSG.CGT.Timmesfeld75.NodeStatement) (hR6 : CardRLeTwo 6) (hRes : Q16Residual)
    (hSym : ∀ (G : Type) [Group G] [Finite G] (M X : Subgroup G) (C : Cfg G M X 6),
      C.PiData → Nat.card ↥(Rc X) ≤ 2 → Function.Surjective C.θ →
        Nat.card ↥(CFSG.Open.pCoreOf 2 M) ≠ 16 → CFSG.Assembly.InCatalog G) :
    EvenN 6 := by
  intro G _ _ M X S
  by_contra hcat
  apply hcat
  have hR := hR6 G M X S hcat
  obtain ⟨C⟩ := exists_cfg_six S
  obtain ⟨D⟩ := C.exists_piData (by norm_num) (by decide)
  by_cases hQ : Nat.card ↥(CFSG.Open.pCoreOf 2 M) = 16
  · exact C.inCatalog_of_card_Q_of_residual hRes hR hQ
  rcases C.theta_alt_or_surjective with halt | hsurj
  · exact D.inCatalog_of_alt hNode hR halt hQ
  · exact hSym G M X C D hR hsurj hQ

theorem evenN_six_of_inputs
    (hR6 : CardRLeTwo 6) (hStroth : StrothSigma6) (hFM : FooteMainL6)
    (hCIT : ClassicalInvolutionTheoremModels) (hYamaki : YamakiSp62CharTwo)
    (hSmith3 : Smith1979WidthThreeCharTwoKP) : EvenN 6 :=
  evenN_six_of_branches SolSeven.nodeStatement_holds hR6 (q16Residual_of_stroth hStroth hFM hCIT)
    fun _ _ _ _ _ C D hR hsurj hQ =>
      Cfg.inCatalog_of_sym_of_residual SolSeven.nodeStatement_holds hYamaki hSmith3
        sixSymResidual_holds C D hR hsurj hQ

end CFSG.RankThree.PartTwo.Sec19.SolEven
