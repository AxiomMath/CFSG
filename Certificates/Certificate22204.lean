
module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsBorelCertInputs
import Certificates.Kernel.LocalComp.L34T1.Glue

public section

namespace Certificates

open CertificateChecks

open CFSG.PSL3Four.Native CFSG.ComponentClassification.GrSLit.L34Facts in
theorem certificate22204 : borelOK = true := KernelLC.L34T1.borel_true

end Certificates
