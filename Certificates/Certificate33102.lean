module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34TwIdxDefs
import Certificates.Kernel.L34Tw.Final
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34TwFinDefs

public section

namespace Certificates

open CertificateChecks

open CFSG.ComponentClassification.GrSLit.L34Tw in
theorem certificate33102 : ∀ x ∈ RA, ∀ y ∈ RA, cosRA (x * y) = cosXor (cosRA x) (cosRA y) :=
  fun x hx y hy => Fin.ext (KernelLC.L34Tw.facts33102 x hx y hy)

end Certificates
