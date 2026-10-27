module

public import CFSG.LocalAnalysis.StandardType.GGQ2CensusFrameAut
import Certificates.Kernel.ExcExt.CensusAll
public import CFSG.LocalAnalysis.StandardType.GGQ2ExcRaw

public section

namespace Certificates

open CFSG.StandardType.GGQ2Frame CFSG.StandardType.GGQ2Frame.ExcRaw in
theorem certificate712513 : ∀ vx : V 2, CensusCasesVx (excRaw 2) vx :=
  CFSG.ExcExtK.censusCasesVx2

end Certificates
