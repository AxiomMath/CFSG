module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExtFrameAut
public import CFSG.LocalAnalysis.StandardType.GGQ2ExcCensusTabs
import Certificates.Kernel.ExcExt.All

public section

namespace Certificates

open CFSG.StandardType.GGQ2Frame CFSG.StandardType.GGQ2Frame.ExcRaw in
theorem certificate712529 : ∀ vx : V 3, 0 ≤ code 3 vx → code 3 vx < 0 + 243 → ExtCasesVx (excRaw 3) vx :=
  fun vx _ _ => CFSG.ExcExtK.extCasesVx3 vx

end Certificates
