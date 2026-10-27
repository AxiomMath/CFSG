module

public import Certificates.Kernel.D4.LinkData
public import Certificates.Kernel.D4.PhiData
public import Certificates.Data.Kernel.D4PhiK
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelD4

theorem phiOK : CFSG.KC.D4Phi.phiK (PH 0) LV LP = true := by quickRfl

end CertificateChecks.KernelD4

end
