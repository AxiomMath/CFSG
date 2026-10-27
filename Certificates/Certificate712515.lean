module

public import CFSG.LocalAnalysis.StandardType.GGQ2CensusFrameAut
import Certificates.Kernel.ExcExt.CensusAll
public import CFSG.LocalAnalysis.StandardType.GGQ2ExcRaw

public section

namespace Certificates

open CFSG.StandardType.GGQ2Frame CFSG.StandardType.GGQ2Frame.ExcRaw in
theorem certificate712515 : ∀ vx : V 4, CensusCasesVx (excRaw 4) vx :=
  CFSG.ExcExtK.censusCasesVx4

end Certificates
