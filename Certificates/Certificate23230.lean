module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5L34CertInputs
import Certificates.Kernel.LocalComp.L34T3.Glue30

public section

namespace Certificates

open CertificateChecks

theorem certificate23230 : CFSG.ComponentClassification.Foote5.L34Unitary.unitaryCheck = true := KernelLC.L34T3.unitary_true

end Certificates
