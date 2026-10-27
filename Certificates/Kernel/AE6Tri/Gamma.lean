module

public import Certificates.Data.Kernel.AE6Tri.Defs
public import Certificates.Kernel.AE6Tri.Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
namespace CertificateChecks.KernelAE6Tri

open CFSG.KC.AE6Tri CFSG.KD.AE6Tri

theorem kGam0 : gamOK RG (diag.getD 0 []) (xc.getD 0 0) (xci.getD 0 0) = true := by quickRfl

theorem kGam1 : gamOK RG (diag.getD 1 []) (xc.getD 1 0) (xci.getD 1 0) = true := by quickRfl

end CertificateChecks.KernelAE6Tri

end
