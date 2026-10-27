module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExtFrameAut
public import CFSG.LocalAnalysis.StandardType.GGQ2ExcCensusTabs
import Certificates.Kernel.ExcExt.All

public section

namespace Certificates

open CFSG.StandardType.GGQ2Frame CFSG.StandardType.GGQ2Frame.ExcRaw in
theorem certificate712528 : ∀ vx : V 2, 0 ≤ code 2 vx → code 2 vx < 0 + 729 → ExtCasesVx (excRaw 2) vx :=
  fun vx _ _ => CFSG.ExcExtK.extCasesVx2 vx

end Certificates
