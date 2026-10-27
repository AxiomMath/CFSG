module

public import CFSG.LocalAnalysis.StandardType.GGQ2CensusFrameAut
import Certificates.Kernel.ExcExt.CensusAll
public import CFSG.LocalAnalysis.StandardType.GGQ2ExcRaw

public section

namespace Certificates

open CFSG.StandardType.GGQ2Frame CFSG.StandardType.GGQ2Frame.ExcRaw in
theorem certificate712514 : ∀ vx : V 3, CensusCasesVx (excRaw 3) vx :=
  CFSG.ExcExtK.censusCasesVx3

end Certificates
