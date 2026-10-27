module

public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityFinal
public import CFSG.RankThree.PartTwo.Sec4.E27.L3FRows
public import CFSG.RankThree.PartTwo.Sec4.E27.D4StepALayer
public import CFSG.RankThree.PartTwo.Sec4.E27.ReeEight
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SecLeaves
public import CFSG.RankThree.PartTwo.Sec4.T444.DiagLeaves
public import CFSG.RankThree.PartTwo.Sec18.Item181b
public import CFSG.RankThree.PartTwo.KFacts.KS18OuterMain
public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityFinalInner

public section

namespace CFSG.RankThree.PartTwo.Sec4

theorem item4_34Sec_holds
    : Item4_34Sec :=
  CFSG.RankThree.PartTwo.Sec4.item4_34Sec_of_leaves
    CFSG.RankThree.PartTwo.Sec19.seitzThreeTrialityWideTwo_holds
    CFSG.RankThree.PartTwo.Sec19.seitzExcAnisotropicTrialityThreeTwo_holds
    (CFSG.RankThree.PartTwo.Sec4.E27.seitz434RestTwentySeven_of_rows
      CFSG.RankThree.PartTwo.Sec4.E27.seitz27L3F_holds
      CFSG.RankThree.PartTwo.Sec4.E27.seitz27_trialityD4_final_layer)
    (CFSG.RankThree.PartTwo.Sec4.E27.seitz434OtherTwentySeven_of_rows
      CFSG.RankThree.PartTwo.Sec4.E27.seitz27_trialityD4_final_layer
      CFSG.RankThree.PartTwo.Sec4.E27.reeF4EightFixPlaneGen_of_certs)

theorem item4_44_3Diag_holds
    : Item4_44_3Diag :=
  CFSG.RankThree.PartTwo.Sec4.item4_44_3Diag_of_item434Sec item4_34Sec_holds

theorem item4_44_1_holds
    : Item4_44_1 :=
  CFSG.RankThree.PartTwo.Sec4.rank3II_4_44_1_of_item4_34 item4_34Sec_holds
    CFSG.RankThree.PartTwo.Sec4.rank3II_4_5

theorem item4_44_2_holds
    : Item4_44_2 :=
  CFSG.RankThree.PartTwo.Sec4.rank3II_4_44_2_of CFSG.RankThree.PartTwo.Sec4.rank3II_4_5
    item4_34Sec_holds

theorem item4_44_3_holds
    : Item4_44_3 :=
  CFSG.RankThree.PartTwo.Sec4.Res4443.item4_44_3_of item4_34Sec_holds
    CFSG.RankThree.PartTwo.Sec4.rank3II_4_5 item4_44_3Diag_holds

end CFSG.RankThree.PartTwo.Sec4

namespace CFSG.RankThree.PartTwo.Sec18

theorem item181_2_holds
    : Item181_2 :=
  CFSG.RankThree.PartTwo.Sec18.rank3II_18_1_2_of
    CFSG.RankThree.PartTwo.Sec4.item4_44_2_holds
    CFSG.RankThree.PartTwo.KFacts.KS18.ks18OuterInvolution

end CFSG.RankThree.PartTwo.Sec18
