module

public import CFSG.LocalAnalysis.StandardType.GGRemTableBLResidualsTwD
public import CFSG.LocalAnalysis.StandardType.GGBstarLIDUnitCopTableB

public section

namespace CFSG.Yardstones.M3f9567aba59d

open CFSG CFSG.Assembly CFSG.StandardType

theorem ggRemainderTableBL_of_residualsUATLABCDEFGUC
    (hCx : GGTableBCxInputOn fun p lab =>
      (((((GGRemainderTableBLResCx p lab ∧ ¬ GGUnitDvdCoprimeNLabel p lab) ∧
          ¬ GGLinTwoLabel p lab) ∧ ¬ GGUnitDvd63CoprimeNLabel p lab) ∧
        ¬ GGUnitDvdLabelNo63 p lab) ∧ ¬ GGOrthLTwDFieldLabel p lab) ∧
        ¬ GGUnitCopFieldLabel p lab)
    (hMod : GGTableBModuleInputOn fun p lab =>
      (((((GGRemainderTableBLResCx p lab ∧ ¬ GGUnitDvdCoprimeNLabel p lab) ∧
          ¬ GGLinTwoLabel p lab) ∧ ¬ GGUnitDvd63CoprimeNLabel p lab) ∧
        ¬ GGUnitDvdLabelNo63 p lab) ∧ ¬ GGOrthLTwDFieldLabel p lab) ∧
        ¬ GGUnitCopFieldLabel p lab)
    (hAct : GGTableBActionInputOn fun p lab =>
      ((((((GGRemainderTableBLResAct p lab ∧ ¬ GGLinDvdLabel p lab) ∧
          ¬ GGUnitDvdCoprimeNLabel p lab) ∧ ¬ GGLinTwoLabel p lab) ∧
          ¬ GGUnitDvd63CoprimeNLabel p lab) ∧ ¬ GGUnitDvdLabelNo63 p lab) ∧
        ¬ GGOrthLTwDFieldLabel p lab) ∧ ¬ GGUnitCopFieldLabel p lab)
    (hX : GGTwE6InnerDiagBound2LInput) (hY : GGE6InnerDiagBoundThreeInput)
    (hLID : GGBstarInnerDiagLInputOn fun p lab =>
      ((((GGRemainderTableBLResLID p lab ∧ ¬ GGUnitDvdLabelNo63 p lab) ∧
        ¬ GGTwE6FieldLabel p lab) ∧ ¬ GGE6ThreeFieldLabel p lab) ∧ ¬ GGOrthLTwDFieldLabel p lab) ∧
        ¬ GGUnitCopFieldLabel p lab)
    (hTv : GGLTransvectionCenterInputOn fun p lab =>
      (GGRemainderTableBLResTv p lab ∧ ¬ GGUnitaryTvResLabel p lab) ∧ ¬ GGLinTwoLabel p lab)
    (hLineN : GGLNoInvariantLineInputOn fun p lab =>
      GGRemainderTableBLResLine p lab ∧ ¬ GGUnitDvdLabel p lab ∧ ¬ GGLinTwoLabel p lab) :
    GGRemainderTableBL :=
  ggRemainderTableBL_of_residualsUATLABCDEFG (ggTableBCxInputOn_of_not_unitCopField hCx)
    (ggTableBModuleInputOn_of_not_unitCopField hMod)
    (ggTableBActionInputOn_of_not_unitCopField hAct) hX hY
    (ggBstarInnerDiagLInputOn_of_not_unitCopField hLID) hTv hLineN

end CFSG.Yardstones.M3f9567aba59d
