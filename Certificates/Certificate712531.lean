module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExtFrameAut
public import CFSG.LocalAnalysis.StandardType.GGQ2ExcCensusTabs
import Certificates.Kernel.ExcExt.All

public section

namespace Certificates

open CFSG.StandardType.GGQ2Frame CFSG.StandardType.GGQ2Frame.ExcRaw in
theorem certificate712531 : ∀ vx : V 4, 547 ≤ code 4 vx → code 4 vx < 547 + 547 → ExtCasesVx (excRaw 4) vx :=
  fun vx _ _ => CFSG.ExcExtK.extCasesVx4 vx

end Certificates
