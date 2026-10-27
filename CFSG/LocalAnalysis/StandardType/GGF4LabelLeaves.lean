module

public import CFSG.LocalAnalysis.StandardType.GGF4LabelH2
public import CFSG.LocalAnalysis.StandardType.GGF4LabelH4Untw
public import CFSG.LocalAnalysis.StandardType.GGF4H5LargeHolds
public import CFSG.LocalAnalysis.StandardType.GGF4LabelH1
public import CFSG.LocalAnalysis.StandardType.GGF4H4ListLinHolds
public import CFSG.LocalAnalysis.StandardType.GGF4H4ListSmallHolds
public import CFSG.LocalAnalysis.StandardType.GGF4H4ListSpHolds
public import CFSG.LocalAnalysis.StandardType.GGF4H4ListExcHolds
public import CFSG.LocalAnalysis.StandardType.GGF4H4Psl64Holds
public import CFSG.LocalAnalysis.StandardType.GGF4LabelH3
public import CFSG.LocalAnalysis.StandardType.GGF4H4JBlockUnitary
public import CFSG.LocalAnalysis.StandardType.GGF4H4TwistedHolds
import CFSG.LocalAnalysis.StandardType.GGInnerDiagMpStdAssembly
public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthKSLOrder

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggSecFiveF4SmallLabelInput_of_leaves
    (hTPn : GGNbrTablePNbrInputNarrow) (hRig : GGLabelRigidInput) (hL : GGLBalanceInput)
    (hP : GGStdSubPrimeInput) (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput)
    (hTP : GGSecFiveA8TablePInput) (hX : GGResXDichotomyInput) (hTCJ : GGTCJKnown)
    (hA8 : GGForkA8NotReflInput) (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    (hFC : GGResNbrFixCentralizesInput) : GGSecFiveF4SmallLabelInput :=
  ggSecFiveF4SmallLabelInput_of_pieces (ggF4LabelH1_holds hTBF hWI) ggF4LabelH2_holds
    (ggF4LabelH3_holds hX hTCJ hRig hTBF hWI hTPn hA8 hraw hiso hFC)
    (ggF4LabelH4_of_pieces_tableP hTPn hRig
      (ggF4H4List_of_families ggF4H4ListSp_holds (ggF4H4ListLin_holds hTBF hWI hL hP)
        (ggF4H4ListExc_holds hTBF hWI hTP) ggF4H4ListSmall_holds)
      (ggF4H4JBlock_holds ggInnerDiagMpInput_holds hRig)
      (ggF4H4Psl64_of_balance hL) (ggF4H4Twisted_of_balance hL hRig hTCJ hP))
    (ggF4LabelH5_of_pos hL hP)

end CFSG.StandardType

end
