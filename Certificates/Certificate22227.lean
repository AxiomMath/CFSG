module

public import Certificates.Data.GrSLitL34FactsCF23HeFixCheck
import Certificates.Kernel.L34W.HjFix
import Certificates.Kernel.L34W.Glue
import CFSG.Certificates.Kernel.L34W.HjFixSound

public section

namespace Certificates

open CertificateChecks

open CFSG.ComponentClassification.GSThmB.CF23L34 in
theorem certificate22227 : hjFixOK = true :=
  CFSG.KC.L34W.hjFixOK_of KernelL34W.t1Of KernelL34W.alOf KernelL34W.bounds_k KernelL34W.gensG
    KernelL34W.y_k KernelL34W.hj_k

end Certificates
