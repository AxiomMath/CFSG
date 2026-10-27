module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsRCertInputs
import Certificates.Kernel.LocalComp.L34RC.Glue

public section

namespace Certificates

open CertificateChecks

open CFSG.PSL3Four.Native CFSG.ComponentClassification.GrSLit.L34Facts in
theorem certificate22207 : rCertOK = true := KernelLC.L34RC.rCert_true

end Certificates
