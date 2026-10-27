module

public import CFSG.LocalAnalysis.StandardType.TableC.POmegaPlusCore
public import CFSG.LocalAnalysis.StandardType.TableC.POmegaMinusCore
public import CFSG.LocalAnalysis.StandardType.TableC.POmegaPlusLift
public import CFSG.LocalAnalysis.StandardType.TableC.POmegaMinusLift
public import CFSG.LocalAnalysis.StandardType.TableC.POmegaCaseA

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank

theorem ggSixTCKnown_POmegaPlus_of_blockDeg
    (hL2 : GGSixTCBlockDegPOmegaPlus) : GGSixTCKnownAt .POmegaPlus :=
  ggSixTCKnown_POmegaPlus_of_dstar
    (ggSixTCDstarPOmegaPlus_of_leaves ggSixTCLiftPOmegaPlus_holds hL2
      ggSixTCCaseAPOmegaPlus_holds)

theorem ggSixTCKnown_POmegaMinus_of_blockDeg
    (hL2 : GGSixTCBlockDegPOmegaMinus) : GGSixTCKnownAt .POmegaMinus :=
  ggSixTCKnown_POmegaMinus_of_dstar
    (ggSixTCDstarPOmegaMinus_of_leaves ggSixTCLiftPOmegaMinus_holds hL2
      ggSixTCCaseAPOmegaMinus_holds)

end CFSG.StandardType

end
