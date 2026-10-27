module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExtFrameAut
public import CFSG.LocalAnalysis.StandardType.GGQ2ExcCensusTabs
import Certificates.Kernel.ExcExt.All

public section

namespace Certificates

open CFSG.StandardType.GGQ2Frame CFSG.StandardType.GGQ2Frame.ExcRaw in
theorem certificate712526 : ∀ vx : V 0, 0 ≤ code 0 vx → code 0 vx < 0 + 81 → ExtCasesVx (excRaw 0) vx :=
  fun vx _ _ => CFSG.ExcExtK.extCasesVx0 vx

end Certificates
