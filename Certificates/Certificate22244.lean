module

public import Certificates.Data.GrSLitL34Sec5SKuActCheck
import Certificates.Kernel.LocalComp.L34KuFinal

public section

namespace Certificates

open CertificateChecks

open CFSG.ComponentClassification.GrSLit.L34Facts.KuAct in
theorem certificate22244 : kuActOK = true := KernelLC.L34Scan.kuAct_true

end Certificates
