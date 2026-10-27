module

public import Certificates.Data.Kernel.D4Q2K.Defs
public import Certificates.Kernel.D4Q2K.Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelD4Q2K

open CFSG.KC.D4Q2K

theorem ch709441pt : ptK D.pts = true := by
  quickRfl

theorem ch709441pt_neg0 : (!ptK (0 :: D.pts)) = true := by
  quickRfl

theorem ch709441pt_negTail : (!ptK D.pts.tail) = true := by
  quickRfl

end CertificateChecks.KernelD4Q2K

end
