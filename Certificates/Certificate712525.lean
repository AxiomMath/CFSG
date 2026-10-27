
module

public import CFSG.LocalAnalysis.StandardType.GGQ2CensusFrameAut
import Certificates.Kernel.ExcExt.InLNbrAll
public import CFSG.LocalAnalysis.StandardType.GGQ2ExcRaw

public section

namespace Certificates

open CFSG.StandardType.GGQ2Frame CFSG.StandardType.GGQ2Frame.ExcRaw in
theorem certificate712525 : ∀ vx : V 4, InLCommonCasesVx (excRaw 4) vx :=
  CFSG.ExcExtK.inLCommonCasesVx4

end Certificates
