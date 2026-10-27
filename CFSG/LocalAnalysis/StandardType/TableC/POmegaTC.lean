module

public import CFSG.LocalAnalysis.StandardType.TableC.POmegaKnown
public import CFSG.LocalAnalysis.StandardType.TableC.POmegaBlockDeg

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank

theorem ggSixTCKnown_POmegaPlus
    : GGSixTCKnownAt .POmegaPlus :=
  ggSixTCKnown_POmegaPlus_of_blockDeg TableC.ggSixTCBlockDegPOmegaPlus_holds

theorem ggSixTCKnown_POmegaMinus
    : GGSixTCKnownAt .POmegaMinus :=
  ggSixTCKnown_POmegaMinus_of_blockDeg TableC.ggSixTCBlockDegPOmegaMinus_holds

end CFSG.StandardType

end
