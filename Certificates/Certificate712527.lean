module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExtFrameAut
public import CFSG.LocalAnalysis.StandardType.GGQ2ExcCensusTabs
import Certificates.Kernel.ExcExt.All

public section

namespace Certificates

open CFSG.StandardType.GGQ2Frame CFSG.StandardType.GGQ2Frame.ExcRaw in
theorem certificate712527 : ∀ vx : V 1, 0 ≤ code 1 vx → code 1 vx < 0 + 81 → ExtCasesVx (excRaw 1) vx :=
  fun vx _ _ => CFSG.ExcExtK.extCasesVx1 vx

end Certificates
