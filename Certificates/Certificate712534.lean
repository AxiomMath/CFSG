module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExtFrameAut
public import CFSG.LocalAnalysis.StandardType.GGQ2ExcCensusTabs
import Certificates.Kernel.ExcExt.All

public section

namespace Certificates

open CFSG.StandardType.GGQ2Frame CFSG.StandardType.GGQ2Frame.ExcRaw in
theorem certificate712534 : ∀ vx : V 5, 0 ≤ code 5 vx → code 5 vx < 0 + 821 → ExtCasesVx (excRaw 5) vx :=
  fun vx _ _ => CFSG.ExcExtK.extCasesVx5 vx

end Certificates
