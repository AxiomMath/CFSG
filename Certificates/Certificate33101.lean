module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34TwRADefs
import Certificates.Kernel.L34Tw.Final

public section

namespace Certificates

open CertificateChecks

open CFSG.ComponentClassification.GrSLit.L34Tw CFSG.ComponentClassification.PSL3Four in
theorem certificate33101 : Nat.card RA = 256 ∧ RA ⊓ S = CFSG.ComponentClassification.GrSLit.L34Facts.T0 := KernelLC.L34Tw.facts33101

end Certificates
