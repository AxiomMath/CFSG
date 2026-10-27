module

public import CFSG.Timmesfeld.ARS.InductionCases
public import CFSG.Timmesfeld.ARS.CaseHFinal
public import CFSG.Timmesfeld.ARS.CaseBMain
public import CFSG.Timmesfeld.ARS.Sec8HypDegenInput
public import CFSG.Timmesfeld.ARS.CaseOAExcl
public import CFSG.Timmesfeld.ARS.CaseOANSLStar
public import CFSG.Timmesfeld.ARS.CaseOADegSU
public import CFSG.Timmesfeld.ARS.CaseMLeviOf
public import CFSG.Timmesfeld.ARS.ExclNSMain
public import CFSG.Timmesfeld.ARS.CaseEMain

public section

namespace CFSG.Timmesfeld

theorem arsInput : ARSInput :=
  ARS.arsInput_of_caseSteps ARS.caseLStep (ARS.caseHStep_of_frameInput ARS.caseHFrameInput)
    ARS.caseBStep
    (ARS.caseMaxStep_of_inputs ARS.degenerate813Input
      (ARS.caseOAStep_of_inputs₄ ARS.oaNonSimplyLacedInput ARS.oaDegenerateInput)
      (ARS.caseMStep_of_frame (Transvection.subgroupTransvectionStatementFrame_of
        (Transvection.transvectionStatementFrame_of_large
          Transvection.transvectionStatementFrameLarge)))
      (ARS.caseEStep_of ARS.ExclNS.caseENonSimplyLacedInput))

end CFSG.Timmesfeld
