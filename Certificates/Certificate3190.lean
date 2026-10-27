module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.WeylAGLData
import Certificates.Kernel.LocalComp.Weyl3190

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSmallLie.OmegaEight CFSG.EvenSmallLie.OmegaEight.Weyl in
theorem certificate3190 : (∀ a b d e : Fin 8, a ≠ b → a ≠ d → b ≠ d → (planeThrough a b d).testBit e = false →
      ∃ τ ∈ Subgroup.closure frameGens, τ 0 = a ∧ τ 1 = b ∧ τ 2 = d ∧ τ 4 = e)
    ∧ (frame16Check = true) := KernelLC.W3190.cert3190

end Certificates
