module

public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineUCoverOdd
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63H5Final
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLCoverSlot
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1III
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1LeavesF8
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1LeavesI1
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1LeavesI2
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1LeavesJ1
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1LeavesZ7
public import CFSG.LocalAnalysis.StandardType.GGYardstoneHeaderImports

public section

namespace CFSG.StandardType

theorem ggLNoInvariantLineInputOn_remainder_of_q2
    (hQ2 : Line63.H5.Line63Q2)
    (hN : GGLNoInvariantLineInputOn fun p lab =>
      Yardstones.M3f9567aba59d.GGRemainderTableBLResLine p lab ∧ ¬ GGUnitDvdLabel p lab ∧
        ¬ GGLinTwoLabel p lab) :
    GGLNoInvariantLineInputOn Yardstones.M3f9567aba59d.GGRemainderTableBLResLine :=
  LineU.ggLNoInvariantLineInputOn_remainder_of_h5 (Line63.H5.ggUnitDvd63BstarRankInput_of_q2 hQ2) hN

end CFSG.StandardType

namespace CFSG.Yardstones.M3f9567aba59d

open CFSG CFSG.Assembly CFSG.StandardType

theorem ggRemainderTableBL_of_residualsUATLQ
    (hCx : GGTableBCxInputOn fun p lab =>
      GGRemainderTableBLResCx p lab ∧ ¬ GGUnitDvdCoprimeNLabel p lab)
    (hMod : GGTableBModuleInputOn fun p lab =>
      GGRemainderTableBLResCx p lab ∧ ¬ GGUnitDvdCoprimeNLabel p lab)
    (hAct : GGTableBActionInputOn fun p lab =>
      GGRemainderTableBLResAct p lab ∧ ¬ GGLinDvdLabel p lab)
    (hLID : GGBstarInnerDiagLInputOn GGRemainderTableBLResLID)
    (hTv : GGLTransvectionCenterInputOn fun p lab =>
      (GGRemainderTableBLResTv p lab ∧ ¬ GGUnitaryTvResLabel p lab) ∧ ¬ GGLinTwoLabel p lab)
    (hQ2 : Line63.H5.Line63Q2)
    (hLineN : GGLNoInvariantLineInputOn fun p lab =>
      GGRemainderTableBLResLine p lab ∧ ¬ GGUnitDvdLabel p lab ∧ ¬ GGLinTwoLabel p lab) :
    GGRemainderTableBL :=
  ggRemainderTableBL_of_residual (ggOrthLTvSCRest_of_signedTorus ggOrthSignedTorusInput_holds
      ggOrthEvenTorusInput_holds) ggTypeADvdNoTransvectionInput_holds
    (ggTableBCxInputOn_of_not_unitDvdCoprimeN hCx)
    (ggTableBModuleInputOn_of_not_unitDvdCoprimeN hMod) (ggTableBActionInputOn_of_not_linDvd hAct)
    hLID
    (ggLTransvectionCenterInputOn_resTv_of_rest (ggLTransvectionCenterInputOn_of_not_linTwo hTv))
    (ggLNoInvariantLineInputOn_remainder_of_q2 hQ2 hLineN)

end CFSG.Yardstones.M3f9567aba59d
