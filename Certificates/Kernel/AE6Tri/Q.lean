module

public import Certificates.Data.Kernel.AE6Tri.Defs
public import Certificates.Kernel.AE6Tri.Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
namespace CertificateChecks.KernelAE6Tri

open CFSG.KC.AE6Tri CFSG.KD.AE6Tri

theorem kPinQ : pinOK RG qw qg = true := by quickRfl

theorem kPinD : pinOK RG delta dg = true := by quickRfl

theorem kQNorm : qnOK RG ml qw qg qnW = true := by quickRfl

theorem kQDelta : qdOK dg qg qw dq qdW = true := by quickRfl

theorem kQDist : qzOK RG qw qg qzW qzJ = true := by quickRfl

end CertificateChecks.KernelAE6Tri

end
