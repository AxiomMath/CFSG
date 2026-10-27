module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisKCertInputs
import Certificates.Kernel.Census.Small.C22607

public section

namespace Certificates

open CertificateChecks

open CFSG.ComponentClassification.GHarris.K3A5 in
theorem certificate22607 : ∀ a b : K, FourPair a b → nCard a b = 36 := KernelCensus.check22607

end Certificates
