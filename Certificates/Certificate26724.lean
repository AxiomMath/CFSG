module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.HNFSound
import Certificates.Kernel.HNFO4.Facts

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.Solomon78 CFSG.Sporadic.HNSchreier in
theorem certificate26724 : 35200 ≤ (conjOrb hnfC0 (hnfRep hnfRepWords[4]!)).ncard := KernelHNFO4.bound4

end Certificates
