module

public import Certificates.Data.Kernel.AE6Tri.DefsC
public import Certificates.Kernel.AE6Tri.Data
public import Certificates.Kernel.AE6Tri.DataC
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
namespace CertificateChecks.KernelAE6Tri

open CFSG.KC.AE6Tri CFSG.KD.AE6Tri

theorem kKC : kcOK RG dg kw kgw cw kU = true := by quickRfl

end CertificateChecks.KernelAE6Tri

end
