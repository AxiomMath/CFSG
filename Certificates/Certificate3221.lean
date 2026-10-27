module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.WeylAbelData
import Certificates.Kernel.LocalComp.Weyl3221

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSmallLie.OmegaEight CFSG.EvenSmallLie.OmegaEight.Weyl in
theorem certificate3221 : PListFacts
    ∧ SubListFacts pPlusGens pPlusIdx pPlusMask pPlusWords
    ∧ SubListFacts q1Gens q1Idx q1Mask q1Words
    ∧ SubListFacts q0Gens q0Idx q0Mask q0Words
    ∧ LayerFacts
    ∧ (lift1Check = true)
    ∧ (lift0Check = true)
    ∧ UListFacts := KernelLC.W3221.cert3221

end Certificates
