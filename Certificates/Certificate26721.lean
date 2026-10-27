module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.HNFSound
import Certificates.Kernel.HNFOrb.Facts

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.Solomon78 CFSG.Sporadic.HNSchreier in
theorem certificate26721 : 1408 ≤ (conjOrb hnfC0 (hnfRep hnfRepWords[1]!)).ncard := KernelHNFOrb.bound1

end Certificates
