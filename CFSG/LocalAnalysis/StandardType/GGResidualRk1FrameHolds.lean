module
public import Certificates.Certificate707001
public import Certificates.Certificate707002
public import Certificates.Certificate707010
public import Certificates.Certificate707011
public import Certificates.Certificate707012
public import Certificates.Certificate709545
public import Certificates.Certificate709548
public import Certificates.Certificate709549
public import Certificates.Certificate709590


import CFSG.LocalAnalysis.StandardType.GGNSJoinQFourFrame
import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylInputHolds
import CFSG.LocalAnalysis.StandardType.GGResCentBoundNbrHolds
import CFSG.LocalAnalysis.StandardType.GGRemTableBLExc11R
import CFSG.LocalAnalysis.StandardType.GGNsq2U62
import CFSG.LocalAnalysis.StandardType.GGTCJHolds
import CFSG.LocalAnalysis.StandardType.GGTPNNarrowC6
import CFSG.LocalAnalysis.StandardType.GGFieldTwoFinal
import CFSG.LocalAnalysis.StandardType.GGK0ExcB3Holds
import CFSG.LocalAnalysis.StandardType.GGSecFiveRemainingHolds
import CFSG.LocalAnalysis.StandardType.GGResidualGenFrameHolds
import CFSG.LocalAnalysis.StandardType.PhanEStdClassified
import CFSG.ClassicalInvolution.Phan.PhanDn.MainA
import CFSG.LocalAnalysis.StandardType.GGFieldTwoCornerSplit
import CFSG.LocalAnalysis.StandardType.GGTCJEnnolaOfUniOrth
import CFSG.LocalAnalysis.StandardType.GGTCJEnnolaUniFinal
import CFSG.LocalAnalysis.StandardType.GGTCJEnnolaOrthFinal
import CFSG.LocalAnalysis.StandardType.GGNSJoinResiduals

public import CFSG.LocalAnalysis.StandardType.GGNbrD4TwoUnitaryBase
import CFSG.LocalAnalysis.StandardType.GGTwE6TwoMember
import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoBridge
import CFSG.LocalAnalysis.StandardType.GGPumpupBalance
import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRefl
import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrOfEnnola
import CFSG.LocalAnalysis.StandardType.GGSecFiveWeakNbr

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly


theorem ggRk1ResidualFrameInputExOf_holds {T : ∀ {ι : Type}, CoxeterMatrix ι → Prop}
    (hRig : GGLabelRigidInput) (hRk : GGTwE6ThreeNbrRankInput) (hFix : GGTBFixInput) (hWA : GGTBFixNbrXInput)
    (hU62 : GGU62OuterDiagInput) (hLB : GGLBalanceInput) (hSP : GGStdSubPrimeInput) (hWI : GGNbrInnerWeylInput)
    (hTCJ : GGTCJKnown) : GGRk1ResidualFrameInputExOf T := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg hns ι M e hpres h3 hA X hX hnsX hXU hmark _
  refine Or.inr ?_
  have hsplit : GGInnerDiagOnLabel (fun p lab =>
      ((¬ GGIsWeylMatrixA M ∧ ¬ NSJoin.NSTypeD M ∧ ggRowP_ETwE6 p lab ∧ lab.n = 1 ∧ X ≠ L) ∧
        (X ≠ L → ¬ NSJoin.NSTypeD M →
          (∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → Nat.card (ggRankOneIn L Bs r) ≠ 6) → lab.n ≠ 1)) ∨
      (lab.n = 1 ∧ ggRowP_EOmP p lab ∧ lab.rank = 4 ∧ X ≠ L ∧ ¬ GGIsWeylMatrixA M ∧ ¬ B < Bs)) p Bs X :=
    hmark.mono' fun _ hl => by
      obtain ⟨h | h, hc⟩ := hl
      · exact Or.inl ⟨h, hc⟩
      · exact Or.inr h
  rcases GGInnerDiagOnLabel.elim_or hsplit with h1 | h2
  ·
    obtain ⟨_, -, -, -, -, -, -, -, ⟨⟨hAM, hDM, -, hn, hXL⟩, hc⟩, -⟩ := largeEvenMarking_exists_hasLabel h1
    have hunG : ¬ ∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → Nat.card (ggRankOneIn L Bs r) ≠ 6 :=
      fun hg => hc hXL hDM hg hn
    have hXK : X ∈ 𝒦 := by
      rcases hX with hXL' | ⟨hXK, -⟩ | ⟨-, hg, -⟩
      · exact absurd hXL' hXL
      · exact hXK
      · exact absurd hg hunG
    exact ggRk1ConclEx_of_twE6Two_member_unguarded hRig hRk ggSecFiveE6QTwoTimmesfeldInput_holds hFix hU62 hWI
      (ggPumpupInput_of_lBalance hLB) hTCJ hcfg hpres h3 hns hAM hDM hunG
      (fun hU => ggRk1ConclEx_of_residualFrameAway (T := T) hRig hRk hFix hWA hU62 hLB hSP hWI hTCJ hcfg hns hpres h3 hA
        (X := L) (Or.inl rfl) hns hU (fun hLL => absurd rfl hLL) fun hLL => absurd rfl hLL)
      hXK hnsX (h1.mono' fun _ hl => ⟨hl.1.2.2.1, hl.1.2.2.2.1⟩)
  ·
    obtain ⟨-, -, -, -, -, -, -, -, ⟨-, -, -, -, hAM, -⟩, -⟩ := largeEvenMarking_exists_hasLabel h2
    have hXw : X = L ∨ GGSecFiveWeakNbr p B Bs x L D J 𝒦 X := by
      rcases hX with hXL | ⟨hXK, -⟩ | ⟨-, -, hw⟩
      · exact Or.inl hXL
      · exact Or.inr (GGSecFiveWeakNbr.of_mem hcfg hXK)
      · exact Or.inr hw
    exact ggRk1ConclEx_of_D4two hRig hcfg hpres h3 hXw hnsX (h2.mono' fun _ hl => ⟨hl.2.1, hl.1, hl.2.2.1⟩) hns hAM

end CFSG.StandardType

namespace CFSG.StandardType.NSJoin

theorem nsNbrQFourInputOf_E_holds
    : NSNbrQFourInputOf (fun {ι : Type} (M : CoxeterMatrix ι) => GGIsWeylMatrixE M) := by
  have hRk := ggTwE6ThreeNbrRankInput_holds
  have hFix := ggTBFixInput_holds
  have hWA := ggTBFixNbrXInput_holds
  have hU62 := ggU62OuterDiagInput_holds
  have hLB := ggLBalanceInput_holds
  have hSP := ggStdSubPrimeInput_holds
  have hWI := ggNbrInnerWeylInput_holds
  have hTCJ := TCJ.ggTCJKnown_holds
  have hRk1F : GGRk1ResidualFrameInputExOf
      (fun {ι : Type} (M : CoxeterMatrix ι) => GGIsWeylMatrixE M) :=
    ggRk1ResidualFrameInputExOf_holds ggLabelRigidInput_holds hRk hFix hWA hU62 hLB hSP hWI hTCJ
  have hGenF := ggGenResidualFrameInputOf_weylE_holds
  have hD := CFSG.ClassicalInvolution.PhanDn.phanDInput2_holds
  have hPE := CFSG.ClassicalInvolution.Phan.PhanE.phanEInput2_holds
  have hT : GGTPNTransferBNoCorners :=
    ggTPNTransferBNoCorners_of_clauses ggNbrSubcomponentInput_proved
      ggTPNTrLocalCore_holds ggTPNTrFlat_holds ggTPNTrCardB_holds ggTPNTrRankB_holds
      ggTPNTrNum_holds ggTPNTrSelfCent_holds
      (ggTPNTrOnly_of_pComp hSP ggPCompCentQuasisimple_holds) ggTPNTrMarked_holds
  have hTP := ggNbrTablePNbrInputOn_fieldTwo_of_leaves hT GGK0ExcB3Prod.ggK0ExcB3_holds
    (ggFieldTwoCorner_of_split ggFieldTwoCorner_rankOne ggFieldTwoCornerNoSL28_holds)
  have hKn := TCJ.ggTCJEnnolaKnown_of_uni_orth TCJ.innDiagAllEnnolaUni TCJ.innDiagAllEnnolaOrth
  exact NSJoin.nsNbrQFourInputOf_E_of_frame ggLabelRigidInput_holds hTCJ hKn hLB hSP hTP
    ggTwE6BigLabelsKnown_holds hRk hD hPE hU62 hFix hWA hWI hRk1F hGenF

end CFSG.StandardType.NSJoin

end
