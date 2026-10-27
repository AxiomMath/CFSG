module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.HNFSound
import Certificates.Kernel.HNF26729.Facts

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.Solomon78 CFSG.Sporadic.HNSchreier in
theorem certificate26729 : 240 ≤ Nat.card ↥(hnfC0 ⊓ Subgroup.centralizer ({hnfRep hnfRepWords[8]!} : Set ↥JH)) := KernelHNF26729.bound

end Certificates
