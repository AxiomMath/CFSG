module

public import CFSG.Timmesfeld.ARS.CaseBMain
public import CFSG.Timmesfeld.ARS.CaseEMain
public import CFSG.Timmesfeld.ARS.CaseHFinal
public import CFSG.Timmesfeld.ARS.CaseMLeviOf
public import CFSG.Timmesfeld.ARS.CaseOADegSU
public import CFSG.Timmesfeld.ARS.CaseOAExcl
public import CFSG.Timmesfeld.ARS.CaseOANSLStar
public import CFSG.Timmesfeld.ARS.ExclNSMain
public import CFSG.Timmesfeld.ARS.InductionCases
public import CFSG.Timmesfeld.ARS.Sec8HypDegenInput

public section

namespace CFSG.RankThree.PartOne.D4RC

open CFSG.Timmesfeld CFSG.Timmesfeld.ARS

theorem rcs_arsOutput {G : Type} [Group G] {R : Set (Subgroup G)} (h : Hyp G R) :
    Output G R :=
  output_of_step (inductionStep_of_cases caseLStep
    (caseHStep_of_frameInput caseHFrameInput) caseBStep
    (caseMaxStep_of_inputs degenerate813Input
      (caseOAStep_of_inputs₄ oaNonSimplyLacedInput oaDegenerateInput)
      (caseMStep_of_frame (Transvection.subgroupTransvectionStatementFrame_of
        (Transvection.transvectionStatementFrame_of_large
          Transvection.transvectionStatementFrameLarge)))
      (caseEStep_of ExclNS.caseENonSimplyLacedInput))) G R h

end CFSG.RankThree.PartOne.D4RC
