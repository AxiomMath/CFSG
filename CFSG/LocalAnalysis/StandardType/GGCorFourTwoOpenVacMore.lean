module

public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoOpenVacMoreCore
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoOpenTableBMore

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGCorFourTwoOpenLIDRest3Label (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGCorFourTwoOpenLIDRestLabel p lab ∧ ¬ GGCorFourTwoVacMoreLabel p lab

@[expose] def GGCorFourTwoOpenTvRest3Label (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGCorFourTwoOpenLabel p lab ∧ ¬ GGCorFourTwoVacMoreLabel p lab

@[expose] def GGCorFourTwoOpenLineRest3Label (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGCorFourTwoOpenLineRestLabel p lab ∧ ¬ GGCorFourTwoVacMoreLabel p lab

@[expose] def GGCorFourTwoOpenTableBVacRest3Label (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGCorFourTwoOpenTableBRest2Label p lab ∧ ¬ GGCorFourTwoVacMoreLabel p lab

section Reductions


theorem ggBstarInnerDiagLInputOn_openLIDRest_of_rest3
    (hSR : TableBExcSmallRanks.GGTwF4ThreeRankInput)
    (h : GGBstarInnerDiagLInputOn GGCorFourTwoOpenLIDRest3Label) :
    GGBstarInnerDiagLInputOn GGCorFourTwoOpenLIDRestLabel :=
  (ggCorFourTwoVacOn_vacMore hSR).bstarInnerDiag h

theorem ggBstarInnerDiagLInputOn_rest3_of_openLIDRest
    (hSR : TableBExcSmallRanks.GGTwF4ThreeRankInput)
    (h : GGBstarInnerDiagLInputOn GGCorFourTwoOpenLIDRestLabel) :
    GGBstarInnerDiagLInputOn GGCorFourTwoOpenLIDRest3Label :=
  (ggCorFourTwoVacOn_vacMore hSR).bstarInnerDiag_rest h

theorem ggLTransvectionCenterInputOn_open_of_rest3
    (hSR : TableBExcSmallRanks.GGTwF4ThreeRankInput)
    (h : GGLTransvectionCenterInputOn GGCorFourTwoOpenTvRest3Label) :
    GGLTransvectionCenterInputOn GGCorFourTwoOpenLabel :=
  (ggCorFourTwoVacOn_vacMore hSR).transvectionCenter h

theorem ggLNoInvariantLineInputOn_lineRest_of_rest3
    (hSR : TableBExcSmallRanks.GGTwF4ThreeRankInput)
    (h : GGLNoInvariantLineInputOn GGCorFourTwoOpenLineRest3Label) :
    GGLNoInvariantLineInputOn GGCorFourTwoOpenLineRestLabel :=
  (ggCorFourTwoVacOn_vacMore hSR).noInvariantLine h

theorem ggTableBCxInputOn_rest2_of_rest3 (hSR : TableBExcSmallRanks.GGTwF4ThreeRankInput)
    (h : GGTableBCxInputOn GGCorFourTwoOpenTableBVacRest3Label) :
    GGTableBCxInputOn GGCorFourTwoOpenTableBRest2Label :=
  (ggCorFourTwoVacOn_vacMore hSR).tableBCx h

theorem ggTableBModuleInputOn_rest2_of_rest3 (hSR : TableBExcSmallRanks.GGTwF4ThreeRankInput)
    (h : GGTableBModuleInputOn GGCorFourTwoOpenTableBVacRest3Label) :
    GGTableBModuleInputOn GGCorFourTwoOpenTableBRest2Label :=
  (ggCorFourTwoVacOn_vacMore hSR).tableBModule h

theorem ggTableBActionInputOn_rest2_of_rest3 (hSR : TableBExcSmallRanks.GGTwF4ThreeRankInput)
    (h : GGTableBActionInputOn GGCorFourTwoOpenTableBVacRest3Label) :
    GGTableBActionInputOn GGCorFourTwoOpenTableBRest2Label :=
  (ggCorFourTwoVacOn_vacMore hSR).tableBAction h

end Reductions

theorem ggLTransvectionCenterInputOn_rest3_of_open
    (h : GGLTransvectionCenterInputOn GGCorFourTwoOpenLabel) :
    GGLTransvectionCenterInputOn GGCorFourTwoOpenTvRest3Label :=
  CorFourTwoVacMore.lTransvectionCenterInputOn_mono (fun _ _ h => h.1) h

theorem ggLNoInvariantLineInputOn_rest3_of_lineRest
    (h : GGLNoInvariantLineInputOn GGCorFourTwoOpenLineRestLabel) :
    GGLNoInvariantLineInputOn GGCorFourTwoOpenLineRest3Label :=
  CorFourTwoVacMore.lNoInvariantLineInputOn_mono (fun _ _ h => h.1) h

theorem ggTableBCxInputOn_rest3_of_rest2 (h : GGTableBCxInputOn GGCorFourTwoOpenTableBRest2Label) :
    GGTableBCxInputOn GGCorFourTwoOpenTableBVacRest3Label :=
  h.mono fun _ _ h => h.1

theorem ggTableBModuleInputOn_rest3_of_rest2
    (h : GGTableBModuleInputOn GGCorFourTwoOpenTableBRest2Label) :
    GGTableBModuleInputOn GGCorFourTwoOpenTableBVacRest3Label :=
  h.mono fun _ _ h => h.1

theorem ggTableBActionInputOn_rest3_of_rest2
    (h : GGTableBActionInputOn GGCorFourTwoOpenTableBRest2Label) :
    GGTableBActionInputOn GGCorFourTwoOpenTableBVacRest3Label :=
  h.mono fun _ _ h => h.1

section Certs


theorem ggCor42Input_of_openRest3 (hK : GGKantorReductionInput)
    (hSR : TableBExcSmallRanks.GGTwF4ThreeRankInput)
    (hLID : GGBstarInnerDiagLInputOn GGCorFourTwoOpenLIDRest3Label)
    (hcen : GGLTransvectionCenterInputOn GGCorFourTwoOpenTvRest3Label)
    (hline : GGLNoInvariantLineInputOn GGCorFourTwoOpenLineRest3Label)
    (hnorm : GGBstarNbrNormalInput) (hgraph : GGNbrGraphInput)
    (hfield : GGNbrFieldTransvectionInput) : GGCor42Input :=
  ggCor42Input_of_openRest hK (ggBstarInnerDiagLInputOn_openLIDRest_of_rest3 hSR hLID)
    (ggLTransvectionCenterInputOn_open_of_rest3 hSR hcen)
    (ggLNoInvariantLineInputOn_lineRest_of_rest3 hSR hline) hnorm hgraph hfield

theorem ggNoTransvectionInput_of_openRest3 (hK : GGKantorReductionInput)
    (hSR : TableBExcSmallRanks.GGTwF4ThreeRankInput)
    (hLID : GGBstarInnerDiagLInputOn GGCorFourTwoOpenLIDRest3Label)
    (hcen : GGLTransvectionCenterInputOn GGCorFourTwoOpenTvRest3Label)
    (hline : GGLNoInvariantLineInputOn GGCorFourTwoOpenLineRest3Label) :
    GGNoTransvectionInput :=
  ggNoTransvectionInput_of_openRest hK (ggBstarInnerDiagLInputOn_openLIDRest_of_rest3 hSR hLID)
    (ggLTransvectionCenterInputOn_open_of_rest3 hSR hcen)
    (ggLNoInvariantLineInputOn_lineRest_of_rest3 hSR hline)

theorem ggTableBCxInput_of_openRest3 (hSR : TableBExcSmallRanks.GGTwF4ThreeRankInput)
    (h : GGTableBCxInputOn GGCorFourTwoOpenTableBVacRest3Label) : GGTableBCxInput :=
  ggTableBCxInput_of_openRest2 (ggTableBCxInputOn_rest2_of_rest3 hSR h)

theorem ggTableBModuleInput_of_openRest3 (hSR : TableBExcSmallRanks.GGTwF4ThreeRankInput)
    (h : GGTableBModuleInputOn GGCorFourTwoOpenTableBVacRest3Label) : GGTableBModuleInput :=
  ggTableBModuleInput_of_openRest2 (ggTableBModuleInputOn_rest2_of_rest3 hSR h)

theorem ggTableBActionInput_of_openRest3 (hSR : TableBExcSmallRanks.GGTwF4ThreeRankInput)
    (h : GGTableBActionInputOn GGCorFourTwoOpenTableBVacRest3Label) : GGTableBActionInput :=
  ggTableBActionInput_of_openRest2 (ggTableBActionInputOn_rest2_of_rest3 hSR h)

end Certs

end CFSG.StandardType

end
