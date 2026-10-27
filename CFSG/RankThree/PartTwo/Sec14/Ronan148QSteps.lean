module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148QNormal
public import CFSG.RankThree.PartTwo.Sec14.Ronan148TLocSteps
public import CFSG.RankThree.PartTwo.Sec14.Item148ProofD4
public import CFSG.RankThree.PartTwo.Sec14.Item148ProofLift
public import CFSG.RankThree.PartTwo.Sec14.Ronan148CFinal4
public import CFSG.RankThree.PartTwo.Sec14.Ronan148NFive
public import CFSG.RankThree.PartTwo.Sec14.Ronan148NKF
public import CFSG.RankThree.PartTwo.Sec4.RonanEpsRowsAssembly
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowsAssembly

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148Q

section

open CFSG.RankThree.PartTwo.Sec14.Ronan148T
open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14

theorem steps148Q_of_frontierLoc
    (hKF : KF148SigL3Loc) (h143 : Item143NNHJ)
    (hPΩ : Step148PointOmega) (hD4D : Step148D4Data) :
    Step148KType ∧ Step148Lift429 ∧ Step148One ∧ Step148Rank ∧ Step148PGL := by
  obtain ⟨h45, h48, h41, h422, -, h415, -, -, h134, -, h142⟩ := Ronan148M.closedInputs
  have hθ : Step148KTheta := step148KTheta_of_loc Sec4.RonanK429.item4_29_holds hKF
  have hKT : Step148KType := step148KType_of_loc hθ hKF
  have hLift : Step148Lift := step148Lift_of_lift429 h45 h48
    (step148Lift429_of_item4_29EpsOuter Sec4.RonanK429.item4_29_holds h41
      Sec4.RonanEps.item4_29EpsOuter_holds)
  have hCentInd : Ronan148N.Step148PGLCentInd :=
    step148PGLCentIndQ_of h134 h48 h415 h422 h45 h142 h143 hPΩ Ronan148C.step148Core_holds
      hKT hLift (step148D4_of_data hD4D)
  exact steps148_of_leavesLoc hKF Sec4.RonanEps.item4_29EpsOuter_holds
    Sec4.RonanK429.item4_29_holds Ronan148N.step148RankFive_holds
    (Ronan148N.step148PGLCent_of_ind' h134 h48 h415 hCentInd)

end

end CFSG.RankThree.PartTwo.Sec14.Ronan148Q
