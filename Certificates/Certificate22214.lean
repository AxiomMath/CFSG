module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsNoFrobCertInputs
import Certificates.Kernel.LocalComp.L34T1.Glue

public section

namespace Certificates

open CertificateChecks

open CFSG.ComponentClassification.GrSLit.L34Facts in
theorem certificate22214 : noFrobOK = true := KernelLC.L34T1.frob_true

end Certificates
