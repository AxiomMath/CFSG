module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.HNFSound
import Certificates.Kernel.HNF26720.Facts

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.Solomon78 CFSG.Sporadic.HNSchreier in
theorem certificate26720 : hnfG1 ∈ Subgroup.centralizer ({aJ} : Set ↥JH) ∧
    hnfG2 ∈ Subgroup.centralizer ({aJ} : Set ↥JH) ∧
    ∀ i j : Fin 9, i ≠ j →
      Disjoint (conjOrb (Subgroup.centralizer ({aJ} : Set ↥JH)) (hnfRep hnfRepWords[i.val]!))
        (conjOrb (Subgroup.centralizer ({aJ} : Set ↥JH)) (hnfRep hnfRepWords[j.val]!)) := KernelHNF26720.facts

end Certificates
