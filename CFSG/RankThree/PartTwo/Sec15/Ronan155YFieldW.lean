module

public import CFSG.RankThree.PartTwo.Sec15.Item154PiProofPoint
public import CFSG.RankThree.PartTwo.Sec15.Item155w3ProofQGen
public import CFSG.RankThree.PartTwo.Sec15.Item155w3ProofHJ
public import CFSG.RankThree.PartTwo.Sec15.Item155w2ProofGrow
public import CFSG.RankThree.PartTwo.Sec14.Ronan148MAssembly3
import CFSG.RankThree.PartTwo.Sec15.Item154PiProof
import CFSG.RankThree.PartTwo.Sec14.Item148Res9Proof
import CFSG.RankThree.PartTwo.Sec17.RouteProvers
import CFSG.RankThree.PartTwo.Sec14.Ronan148TIdSubMain
public import CFSG.RankThree.PartTwo.Sec15.Item1523Proof
public import CFSG.RankThree.PartTwo.Sec15.Item155R2Proof
public import CFSG.RankThree.PartTwo.Sec15.Item155R2ProofSteps
public import CFSG.RankThree.PartTwo.Sec14.Concl142Item

public section

namespace CFSG.RankThree.PartTwo.Sec15.Ronan155Y

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14

section Y4

theorem y4LThreePiNHJR_holds
    : Y4LThreePiNHJR := by
  obtain ⟨h45, h48, h41, h422, h46, h415, hGW, h131, h134, -, h142⟩ := Ronan148M.closedInputs
  have h425 : Sec4.Item4_25Fix := Sec4.Ronan148S.item4_25Fix_holds
  have h143Q : Ronan148Q.Item143QS14 :=
    Ronan148Q.item143QS14_of_items h45 h48 h41 hGW h134 KFacts.kpSz Ronan148D.onTripleGenE27
      (Ronan148K.ks143LBalComp2_of_open h41
        Ronan148K.k143OpenChar2_holds.toLie.toNoSuz.toK143Open) h425
      (Ronan148D.step143HJCompRank_of h134 h48)
      (Ronan148D.step143HJCompM24_of h425 h41 hGW h134 h48)
  have h143 : Ronan148Q.Item143NNHJ := Ronan148Q.item143NNHJ_of_item143QS14 h134 h48 h415 h143Q
  have hD4D : Step148D4Data :=
    Ronan148Q.step148D4DataQ_of_kf Ronan148B.kF148D4Comm_holds h422 h45 h142 h134 h48 h415 h143
  have hc142 : Concl142S14 := Ronan148M.concl142S14_holds
  have hc143 : Concl143S14 := fun G _ _ A c L hs =>
    Ronan148Q.concl143_of_item143Q (h143Q G A c L hs)
  have hPΩ : Step148PointOmega := Ronan148B.step148PointOmega_of_sigF h131 hc142 h46 h41
    (Ronan148B.kf148PointSigF_of_insp (Ronan148B.kf148PointSigInsp_of_sigGenL3
      (Ronan148B.kf148SigGenL3_of_ident (Ronan148T.kf148SigGenL3Ident_of_sub Ronan148T.subHeis148))))
  obtain ⟨hKT, hLift429, -, -, -⟩ :=
    Ronan148Q.steps148Q_of_frontierLoc
      (Ronan148T.kf148SigL3Loc_of_inspectLoc Ronan148T.inspectSig148L3Loc) h143 hPΩ hD4D
  have hPHJ : Step148PointHJ := step148PointHJ_of_res2 hc143 h134 h48 h422 h45 h142 hPΩ
    (Ronan148H.step148PointHJdONGenD_of_comp hc143 h46 Ronan148H.kf148OneLineComp_holds)
  have hPoint : Step148Point :=
    Ronan148Q.step148PointQ_of h422 h45 h142 h143Q hPΩ (Ronan148Q.step148PointHJQ_of hPHJ)
  exact y4LThreePiNHJR_of h134 h48 Ronan148C.step148Core_holds hPoint hKT
    (step148Lift_of_lift429 h45 h48 hLift429) (step148D4_of_data hD4D) step148KTypeSigma_holds

theorem step155GrowAltTwoFieldWR_holds
    : Step155GrowAltTwoFieldWR :=
  step155GrowAltTwoFieldWR_of_y4LThreePi y4LThreePiNHJR_holds

end Y4

section Two

theorem step155GrowAltTwoWR_holds
    : Step155GrowAltTwoWR := by
  obtain ⟨-, h48, -, -, -, h415, -, -, h134, -, -⟩ := Ronan148M.closedInputs
  exact step155GrowAltTwoWR_of_y4LThreePi Ronan148M.item148R_holds
    (item145BotS14_of h134 h48 h415) y4LThreePiNHJR_holds

theorem step155GrowAltWR_holds
    : Step155GrowAltWR :=
  step155GrowAltWR_of_two step155GrowAltTwoWR_holds

end Two

end CFSG.RankThree.PartTwo.Sec15.Ronan155Y
