module

public import CFSG.LocalAnalysis.StandardType.GGQ2CensusFrameAut
public import CFSG.LocalAnalysis.StandardType.GGQ2ExcCensusTabs
import Certificates.Kernel.ExcExt.CensusAll

public section

namespace Certificates

open CFSG.StandardType.GGQ2Frame CFSG.StandardType.GGQ2Frame.ExcRaw in
theorem certificate712519 : ∀ vx : V 5, 1642 ≤ code 5 vx → code 5 vx < 1642 + 821 → CensusCasesVx (excRaw 5) vx :=
  fun vx _ _ => CFSG.ExcExtK.censusCasesVx5 vx

end Certificates
