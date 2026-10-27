module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.HNFSound
import Certificates.Kernel.HNFSub.Facts

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.Solomon78 CFSG.Sporadic.HNSchreier in
theorem certificate26727 : 354816 ≤ (conjOrb hnfC0 (hnfRep hnfRepWords[7]!)).ncard := KernelHNFSub.bound7

end Certificates
