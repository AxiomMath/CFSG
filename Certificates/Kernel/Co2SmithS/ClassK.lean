module

public import Certificates.Kernel.Co2SmithS.ClassData
public import Certificates.Kernel.Co2SmithS.Lets
public import Certificates.Data.Kernel.Co2SmithS.Class
import CFSG.Certificates.Kernel.Common.Cover

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelCo2SmithS

open CFSG.KC.Co2SmithS

theorem class_ok : ∀ k < 56925, classRecK CF (LT 0) (LT 1) (powV (LT 1) 4) 56925 k = true := by
  kc_cover 512

end CertificateChecks.KernelCo2SmithS

end
