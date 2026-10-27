module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExtFrameAut
public import CFSG.LocalAnalysis.StandardType.GGQ2ExcCensusTabs
import Certificates.Kernel.ExcExt.All

public section

namespace Certificates

open CFSG.StandardType.GGQ2Frame CFSG.StandardType.GGQ2Frame.ExcRaw in
theorem certificate712538 : ∀ vx : V 5, 3284 ≤ code 5 vx → code 5 vx < 3284 + 821 → ExtCasesVx (excRaw 5) vx :=
  fun vx _ _ => CFSG.ExcExtK.extCasesVx5 vx

end Certificates
