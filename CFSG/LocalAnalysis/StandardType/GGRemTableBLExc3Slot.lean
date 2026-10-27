module

public import CFSG.Yardstones.M3f9567aba59d.TableBL
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLExc3
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLExcReductionSlot

public section

namespace CFSG.Yardstones.M3f9567aba59d

open CFSG CFSG.Assembly CFSG.StandardType

theorem ggRemainderTableBL_of_exc3
    (hCx : GGTableBCxInputOn GGRemTableBLExc3Label)
    (hMod : GGTableBModuleInputOn GGRemTableBLExc3Label)
    (hAct : GGTableBActionInputOn GGRemTableBLExc3Label)
    (hX : GGTwE6InnerDiagBound2LInput) (hY : GGE6InnerDiagBoundThreeInput)
    (hM : GGTwE6TorusModelInput) (hT : GGTwE6NoTransvectionInput)
    (hTv : GGLTransvectionCenterInputOn GGRemTableBLExc3Label)
    (hLineN : GGLNoInvariantLineInputOn GGRemTableBLExc3Label) :
    GGRemainderTableBL := by
  have hCx1 : GGTableBCxInputOn
      (fun p lab => GGRemTableBLExc2Label p lab ∧ ¬ GGTwE6TBLabel p lab) :=
    GGTableBCxInputOn.mono (fun p lab h => ggRemTableBLExc3Label_of_exc2 p lab h) hCx
  have hMod1 : GGTableBModuleInputOn
      (fun p lab => GGRemTableBLExc2Label p lab ∧ ¬ GGTwE6TBLabel p lab) :=
    ggTableBModuleInputOn_mono_exc (fun p lab h => ggRemTableBLExc3Label_of_exc2 p lab h) hMod
  have hAct1 : GGTableBActionInputOn
      (fun p lab => GGRemTableBLExc2Label p lab ∧ ¬ GGTwE6TBLabel p lab) :=
    ggTableBActionInputOn_mono_exc (fun p lab h => ggRemTableBLExc3Label_of_exc2 p lab h) hAct
  have hTv1 : GGLTransvectionCenterInputOn
      (fun p lab => GGRemTableBLExc2Label p lab ∧ ¬ GGTwE6TBLabel p lab) :=
    CorFourTwoVacMore.lTransvectionCenterInputOn_mono
      (fun p lab h => ggRemTableBLExc3Label_of_exc2 p lab h) hTv
  have hLine1 : GGLNoInvariantLineInputOn
      (fun p lab => GGRemTableBLExc2Label p lab ∧ ¬ GGTwE6TBLabel p lab) :=
    CorFourTwoVacMore.lNoInvariantLineInputOn_mono
      (fun p lab h => ggRemTableBLExc3Label_of_exc2 p lab h) hLineN
  exact ggRemainderTableBL_of_exc'
    (ggTableBCxInputOn_of_not_twE6TB_of_model hX hM hCx1)
    (ggTableBModuleInputOn_of_not_twE6TB_of_model hX hM hMod1)
    (ggTableBActionInputOn_of_not_twE6TB_of_model hX hM hAct1) hX hY
    (ggLTransvectionCenterInputOn_of_not_twE6TB hT hTv1)
    (ggLNoInvariantLineInputOn_of_not_twE6TB_of_model hM hLine1)

end CFSG.Yardstones.M3f9567aba59d

end
