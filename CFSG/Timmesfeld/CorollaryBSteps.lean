module

public import CFSG.Timmesfeld.Assembly

public section

namespace CFSG.Timmesfeld.CorB

theorem largeStepSE_holds : Bridge.LargeStepSE :=
  have hT : Moufang.Tim75Thm31 := Bridge.tim75Thm31
  have hK : Bridge.ThirdKindStep :=
    Bridge.RootClosure.thirdKindStep_of_rootThreeL2 Bridge.commonNeighbour hT
      (Bridge.RootClosure.rootThreeL2Stmt_of Bridge.RootClosure.psl2SylowCoordStmt
        Bridge.RootClosure.l2TorusIrredStmt Bridge.RootClosure.naturalComplementStmt)
  Bridge.largeStepSE_of_third hK Bridge.gammaResidualStep
    (Bridge.commLambdaStep_of_nCore (Bridge.nCoreStep_of_nCoreStepLarge Bridge.nCoreStepLarge))
    (Bridge.existsCommSpecStepE_of_thin hT Bridge.nCoreStepLarge
      (Bridge.thinOneOppositeStepE_of_split
        (Bridge.thinManyStepE_of Bridge.rootLinesPowerStep Bridge.rootLinesTorusStep
          (Bridge.thinGateManyStep_of
            (Bridge.thinGateCoreStep_of
              (Bridge.thinGateCoreSmallStep_of Bridge.thinGateCenterStep Bridge.thinGateIrrStep)
              Bridge.thinGateCoreOneStep))
          (Bridge.RootOne.thinGateOneStep_of Bridge.thinGateOne_kOne))
        (Bridge.thinTwoStepE_of_thinAllBadFalse openInputs_holds.thinAllBadFalse)))

theorem exceptionalGlobalStepNJ2_holds : Moufang.ExceptionalGlobalStepNJ2 :=
  Moufang.exceptionalGlobalStepNJ2_of_noPlane (Moufang.exceptionalNoPlaneStepNJ2_of_cases
    (Moufang.exceptionalLeviStep_of_tim75 Bridge.tim75Thm31 Bridge.caseICommPQInput_holds)
    Bridge.exceptionalNoLeviPlaneStep_holds
    (Moufang.exceptionalNoLeviTO5StepNJ2_of_diam4
      (Moufang.excDiam4InputNJ2_of Moufang.Deep.excThreeNearInput
        openInputs_holds.exceptionalCyc)))

theorem commConnected_holds : ∀ (G : Type) [Group G] (D : Set G), Hyp G D →
    Moufang.NoPolar D → Closure.CommConnected D :=
  fun _ _ _ hH' hNP => Bridge.commConnected_of_noPolar
    (Bridge.asc73Input_of_theoremTwo CFSG.ShultStronglyClosedTI.theoremTwo) hH' hNP

end CFSG.Timmesfeld.CorB
