module

public import CFSG.LocalAnalysis.StandardType.GGQ2CensusFrameAut
import Certificates.Kernel.ExcExt.CensusAll
public import CFSG.LocalAnalysis.StandardType.GGQ2ExcRaw

public section

namespace Certificates

open CFSG.StandardType.GGQ2Frame CFSG.StandardType.GGQ2Frame.ExcRaw in
theorem certificate712511 : ∀ vx : V 0, CensusCasesVx (excRaw 0) vx :=
  CFSG.ExcExtK.censusCasesVx0

end Certificates
