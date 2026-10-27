module

public import CFSG.Yardstones.M3f9567aba59d.TableBL
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLExcReduction
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLResidualsUni2

public section

namespace CFSG.Yardstones.M3f9567aba59d

open CFSG CFSG.Assembly CFSG.StandardType

theorem ggRemainderTableBL_of_exc
    (hCx : GGTableBCxInputOn GGRemTableBLExcLabel)
    (hMod : GGTableBModuleInputOn GGRemTableBLExcLabel)
    (hAct : GGTableBActionInputOn GGRemTableBLExcLabel)
    (hX : GGTwE6InnerDiagBound2LInput) (hY : GGE6InnerDiagBoundThreeInput)
    (hTv : GGLTransvectionCenterInputOn GGRemTableBLExcLabel)
    (hLineN : GGLNoInvariantLineInputOn GGRemTableBLExcLabel) :
    GGRemainderTableBL :=
  ggRemainderTableBL_of_residualsUni
    (ggTableBCxInputOn_restrict_exc hCx fun p lab hp h1 h2 h3 =>
      ggRemTableBLExc_of_resCx hp h1 h2 h3)
    (ggTableBModuleInputOn_restrict_exc hMod fun p lab hp h1 h2 h3 =>
      ggRemTableBLExc_of_resCx hp h1 h2 h3)
    (ggTableBActionInputOn_restrict_exc hAct fun p lab hp h1 h2 h3 =>
      ggRemTableBLExc_of_resCx hp h1 h2 (ggRemTableBLExcResCx_of_act h3))
    hX hY ggBstarInnerDiagLInputOn_resLID_false
    (ggLTransvectionCenterInputOn_of_not_unitDvd63All
      (ggLTransvectionCenterInputOn_restrict_exc hTv fun p lab hp h1 h2 h3 =>
        ggRemTableBLExc_of_resTv hp h1 h2 (And.intro h3.1.1 h3.2)))
    (ggLNoInvariantLineInputOn_restrict_exc hLineN fun p lab hp h1 h2 h3 =>
      ggRemTableBLExc_of_resLine hp h1 h2 h3)

theorem ggRemainderTableBL_of_exc'
    (hCx : GGTableBCxInputOn GGRemTableBLExc2Label)
    (hMod : GGTableBModuleInputOn GGRemTableBLExc2Label)
    (hAct : GGTableBActionInputOn GGRemTableBLExc2Label)
    (hX : GGTwE6InnerDiagBound2LInput) (hY : GGE6InnerDiagBoundThreeInput)
    (hTv : GGLTransvectionCenterInputOn GGRemTableBLExc2Label)
    (hLineN : GGLNoInvariantLineInputOn GGRemTableBLExc2Label) :
    GGRemainderTableBL := by
  have hCx1 : GGTableBCxInputOn
      (fun p lab => GGRemTableBLExcLabel p lab ∧ ¬ GGE6TwoThreeLabel p lab) :=
    GGTableBCxInputOn.mono (fun p lab h => ggRemTableBLExc2Label_of_exc p lab h) hCx
  have hMod1 : GGTableBModuleInputOn
      (fun p lab => GGRemTableBLExcLabel p lab ∧ ¬ GGE6TwoThreeLabel p lab) :=
    ggTableBModuleInputOn_mono_exc (fun p lab h => ggRemTableBLExc2Label_of_exc p lab h) hMod
  have hAct1 : GGTableBActionInputOn
      (fun p lab => GGRemTableBLExcLabel p lab ∧ ¬ GGE6TwoThreeLabel p lab) :=
    ggTableBActionInputOn_mono_exc (fun p lab h => ggRemTableBLExc2Label_of_exc p lab h) hAct
  have hTv1 : GGLTransvectionCenterInputOn
      (fun p lab => GGRemTableBLExcLabel p lab ∧ ¬ GGE6TwoThreeLabel p lab) :=
    CorFourTwoVacMore.lTransvectionCenterInputOn_mono
      (fun p lab h => ggRemTableBLExc2Label_of_exc p lab h) hTv
  have hLine1 : GGLNoInvariantLineInputOn
      (fun p lab => GGRemTableBLExcLabel p lab ∧ ¬ GGE6TwoThreeLabel p lab) :=
    CorFourTwoVacMore.lNoInvariantLineInputOn_mono
      (fun p lab h => ggRemTableBLExc2Label_of_exc p lab h) hLineN
  exact ggRemainderTableBL_of_exc
    (ggTableBCxInputOn_of_not_e6TwoThree hCx1)
    (ggTableBModuleInputOn_of_not_e6TwoThree hMod1)
    (ggTableBActionInputOn_of_not_e6TwoThree hAct1) hX hY
    (ggLTransvectionCenterInputOn_of_not_e6TwoThree hTv1)
    (ggLNoInvariantLineInputOn_of_not_e6TwoThree hLine1)

end CFSG.Yardstones.M3f9567aba59d

end
