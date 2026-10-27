module

public import CFSG.LocalAnalysis.StandardType.GGNbrWeylTypeNonSplit
public import CFSG.LocalAnalysis.StandardType.GGNbrWeylTypeSplit
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplitVac
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplitClassical
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplitExcPlusHolds
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplitE6Two
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplitTwE6SplitHolds
public import CFSG.LocalAnalysis.StandardType.GGUSixThreeWeylHolds
import CFSG.LocalAnalysis.StandardType.GGNbrWeylTypeVac
import CFSG.LocalAnalysis.StandardType.GGNbrWeylTypeUnitary
import CFSG.LocalAnalysis.StandardType.GGNbrWeylTypeUnitaryHyp
import CFSG.LocalAnalysis.StandardType.GGNbrWeylTypeOrth
import CFSG.LocalAnalysis.StandardType.GGNbrWeylTypeSympLin
import CFSG.LocalAnalysis.StandardType.GGNbrWeylTypeExcPlus
import CFSG.LocalAnalysis.StandardType.GGNbrWeylTypeE6Two
import CFSG.LocalAnalysis.StandardType.GGNbrWeylTypeTwE6
import CFSG.LocalAnalysis.StandardType.GGNbrWeylTypeF4Three
import CFSG.LocalAnalysis.StandardType.GGNbrWeylTypeUSixThree
import CFSG.LocalAnalysis.StandardType.GGNbrWeylTypeTwE6Three
import CFSG.LocalAnalysis.StandardType.GGNbrWeylTypeSplitA
import CFSG.LocalAnalysis.StandardType.GGNbrWeylTypeSplitBC
import CFSG.LocalAnalysis.StandardType.GGNbrWeylTypeSplitD
import CFSG.LocalAnalysis.StandardType.GGNbrWeylTypeSplitE6Three
import CFSG.LocalAnalysis.StandardType.GGNbrWeylTypeSplitExc
import CFSG.LocalAnalysis.StandardType.GGNbrWeylTypeExcSeven
import CFSG.LocalAnalysis.StandardType.GGLabelRigid
import CFSG.LocalAnalysis.StandardType.GGNbrCenterPCyclicHolds

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

theorem ggSecFivePumpNbrNSInput_holds
    (hF4R : GGF4ThreeNbrRankInput) (hL : GGLBalanceInput) (hPJ : GGStdSubPrimeInput)
    (hR : GGTwE6ThreeNbrRankInput) (hTCJ : GGTCJKnown) (hTP : GGSecFiveA8TablePInput)
    (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput) :
    GGSecFivePumpNbrNSInput := by
  have hRig : GGLabelRigidInput := ggLabelRigidInput_holds
  have hZ : GGNbrBstarCenterInput :=
    ggNbrBstarCenterInput_of_centerPCyclic ggLabelCenterPCyclicInput_holds
  have hW := ggNbrTableBWeylTypeNonSplitOn_of_families ggNbrTableBWeylTypeNonSplitOn_vac
    ggNbrTableBWeylTypeNonSplitOn_unitary ggNbrTableBWeylTypeNonSplitOn_unitaryHyp
    ggNbrTableBWeylTypeNonSplitOn_orth ggNbrTableBWeylTypeNonSplitOn_sympLin
    ggNbrTableBWeylTypeNonSplitOn_excPlus ggNbrTableBWeylTypeNonSplitOn_e6Two
    ggNbrTableBWeylTypeNonSplitOn_twE6
  have hNS := ggNbrWeylTypeNonSplitInput_of_weylType hW hF4R hL hPJ
    ggF4ThreeNbrWeylTypeInput_holds ggUSixThreeNbrWeylTypeInput_holds
  have hFull := ggNbrWeylTypeNonSplitFull_of_rank hNS hR ggTwE6ThreeNbrWeylTypeInput_holds hRig hZ
  have hSplit := ggNbrTableBWeylTypeSplitInput_of_families ggNbrTableBWeylTypeSplitOn_typeA
    ggNbrTableBWeylTypeSplitOn_typeBC ggNbrTableBWeylTypeSplitOn_typeD
    ggNbrTableBWeylTypeSplitOn_exc ggNbrTableBWeylTypeSplitOn_e6Three
  exact ggSecFivePumpNbrNSInput_of_parts (ggSecFivePumpNbrNSSplitInput_of_weylType hSplit hRig hZ)
    (ggNbrExcSevenReflInput_holds hRig hTCJ hTP) hFull hraw hiso

end CFSG.StandardType

end
