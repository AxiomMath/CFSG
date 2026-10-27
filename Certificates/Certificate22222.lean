module

public import Certificates.Data.GrSLitL34FactsCF23Check
import Certificates.Kernel.L34W.InvFix
import Certificates.Kernel.L34W.Glue
import CFSG.Certificates.Kernel.L34W.InvFixSound

public section

namespace Certificates

open CertificateChecks

open CFSG.ComponentClassification.GrSLit.L34Facts.Real in
theorem certificate22222 : invFixOK = true :=
  CFSG.KC.L34W.invFixOK_of KernelL34W.t1Of KernelL34W.alOf KernelL34W.bounds_k KernelL34W.gensG
    KernelL34W.y_k KernelL34W.cf22_k

end Certificates
