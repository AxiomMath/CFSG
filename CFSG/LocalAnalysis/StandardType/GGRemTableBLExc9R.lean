module

public import CFSG.LocalAnalysis.StandardType.GGTableBF4TwoTBIrred
public import CFSG.LocalAnalysis.StandardType.GGTableBF4TwoTBTv
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLExc6R
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6TwoThreeAct
public import CFSG.LocalAnalysis.StandardType.GGExcFrameNormIso
public import CFSG.LocalAnalysis.StandardType.GGExcFrameNormIsoF4

public section

namespace CFSG.Yardstones.M3f9567aba59d

open CFSG CFSG.Assembly CFSG.StandardType CFSG.StandardType.TableBF4TwoTB

theorem ggRemainderTableBL_of_exc9r
    (hO : GGTwE6TwoThreeActionOddInput)
    (hS : GGF4TwoNonToralSolvInput)
    (hX : GGTwE6InnerDiagBound2LInput) (hY : GGE6InnerDiagBoundThreeInput)
    (hM : GGTwE6TorusModelInput) (hT : GGTwE6NoTransvectionInput)
    (hKT : GGE6DivTorusNbrInput) (hKM : GGE6DivModuleInput) (hKA : GGE6DivActionInput)
    (hKV : GGE6DivTvInput) (hE7 : TableBExcTwoTB.GGE7TwoSCToralInput)
    (hE8 : TableBExcTwoTB.GGE8TwoSCToralInput) (hB : GGTwE6ThreeBstarRankInput)
    (hTN : GGTwE6ThreeTorusNbrInput) (hTM : GGTwE6ThreeModuleInput)
    (hTA : GGTwE6ThreeActionInputQ8) (hTT : GGTwE6ThreeTvInput) :
    GGRemainderTableBL :=
  ggRemainderTableBL_of_exc6r (ggTableBCxInputOn_f4TwoThree_holds hS)
      (ggTableBModuleInputOn_f4TwoThree_holds hS)
      ((ggTableBActionInputOn_f4TwoThree_holds hS).or (ggTableBActionInputOn_twE6TwoThree hB hO))
      (ggLTransvectionCenterInputOn_f4TwoThree_holds hS ExcFrameIso.ggF4TwoNormIsometryInput_holds)
      (ggLNoInvariantLineInputOn_f4TwoThree_holds hS) hX hY hM hT hKT hKM hKA hKV hE7 hE8
      ExcFrameIso.ggE7TwoNormIsometryInput_holds ExcFrameIso.ggE8TwoNormIsometryInput_holds hB hTN
      hTM hTA hTT

end CFSG.Yardstones.M3f9567aba59d

end
