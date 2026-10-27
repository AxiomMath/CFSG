module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsGraphCertInputs
import Certificates.Kernel.LocalComp.L34Graph.Final

public section

namespace Certificates

open CertificateChecks

open CFSG.PSL3Four.Native CFSG.ComponentClassification.GrSLit.L34Facts in
theorem certificate22210 : graphOK = true := KernelLC.L34Graph.graphOK_true

end Certificates
