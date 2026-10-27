module

public import CFSG.Yardstones.M3f9567aba59d.TableBL
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLExc4
public import CFSG.LocalAnalysis.StandardType.GGTableBThreeTBE6
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLExc3Slot

public section

namespace CFSG.Yardstones.M3f9567aba59d

open CFSG CFSG.Assembly CFSG.StandardType CFSG.StandardType.TableBExcTwoTB

theorem ggRemainderTableBL_of_exc4
    (hCx : GGTableBCxInputOn GGRemTableBLExc4Label)
    (hMod : GGTableBModuleInputOn GGRemTableBLExc4Label)
    (hAct : GGTableBActionInputOn GGRemTableBLExc4Label)
    (hX : GGTwE6InnerDiagBound2LInput) (hY : GGE6InnerDiagBoundThreeInput)
    (hM : GGTwE6TorusModelInput) (hT : GGTwE6NoTransvectionInput)
    (hTv : GGLTransvectionCenterInputOn GGRemTableBLExc4TvLabel)
    (hLineN : GGLNoInvariantLineInputOn GGRemTableBLExc4Label)
    (hKT : GGE6DivTorusNbrInput) (hKM : GGE6DivModuleInput) (hKA : GGE6DivActionInput)
    (hKV : GGE6DivTvInput) (hE7 : GGE7TwoSCToralInput) (hE8 : GGE8TwoSCToralInput) :
    GGRemainderTableBL := by
  have hCx1 : GGTableBCxInputOn fun p lab =>
      GGRemTableBLExc3Label p lab ∧ ¬ GGTableBE6DivLabel p lab :=
    ggTableBCxInputOn_of_not_e7TwoThree hE7 (ggTableBCxInputOn_of_not_e8TwoThree hE8
      (GGTableBCxInputOn.mono (fun p lab h => ggRemTableBLExc4Label_of p lab h) hCx))
  have hMod1 : GGTableBModuleInputOn fun p lab =>
      GGRemTableBLExc3Label p lab ∧ ¬ GGTableBE6DivLabel p lab :=
    ggTableBModuleInputOn_of_not_e7TwoThree hE7 (ggTableBModuleInputOn_of_not_e8TwoThree hE8
      (ggTableBModuleInputOn_mono_exc (fun p lab h => ggRemTableBLExc4Label_of p lab h) hMod))
  have hAct1 : GGTableBActionInputOn fun p lab =>
      GGRemTableBLExc3Label p lab ∧ ¬ GGTableBE6DivLabel p lab :=
    ggTableBActionInputOn_of_not_e7TwoThree hE7 (ggTableBActionInputOn_of_not_e8TwoThree hE8
      (ggTableBActionInputOn_mono_exc (fun p lab h => ggRemTableBLExc4Label_of p lab h) hAct))
  have hLine1 : GGLNoInvariantLineInputOn fun p lab =>
      GGRemTableBLExc3Label p lab ∧ ¬ GGTableBE6DivLabel p lab :=
    ggLNoInvariantLineInputOn_of_not_e7TwoThree hE7 (ggLNoInvariantLineInputOn_of_not_e8TwoThree
      hE8 (CorFourTwoVacMore.lNoInvariantLineInputOn_mono
        (fun p lab h => ggRemTableBLExc4Label_of p lab h) hLineN))
  have hTv1 : GGLTransvectionCenterInputOn fun p lab =>
      GGRemTableBLExc3Label p lab ∧ ¬ GGTableBE6DivLabel p lab :=
    CorFourTwoVacMore.lTransvectionCenterInputOn_mono
      (fun p lab h => ggRemTableBLExc4TvLabel_of p lab h) hTv
  exact ggRemainderTableBL_of_exc3 (ggTableBCxInputOn_of_not_e6Div hY hKT hCx1)
      (ggTableBModuleInputOn_of_not_e6Div hY hKM hMod1)
      (ggTableBActionInputOn_of_not_e6Div hY hKA hAct1) hX hY hM hT
      (ggLTransvectionCenterInputOn_of_not_e6Div hKV hTv1)
      (ggLNoInvariantLineInputOn_of_not_e6Div hKM hLine1)

end CFSG.Yardstones.M3f9567aba59d

end
