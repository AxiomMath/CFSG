module

public import CFSG.LocalAnalysis.StandardType.GGQ2CensusFrameAut
public import CFSG.LocalAnalysis.StandardType.GGQ2ExcCensusTabs
import Certificates.Kernel.ExcExt.CensusAll

public section

namespace Certificates

open CFSG.StandardType.GGQ2Frame CFSG.StandardType.GGQ2Frame.ExcRaw in
theorem certificate712522 : ∀ vx : V 5, 4105 ≤ code 5 vx → code 5 vx < 4105 + 821 → CensusCasesVx (excRaw 5) vx :=
  fun vx _ _ => CFSG.ExcExtK.censusCasesVx5 vx

end Certificates
