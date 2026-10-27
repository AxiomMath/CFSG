module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.WeylData
import Certificates.Kernel.LocalComp.Weyl3184Facts

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSmallLie.OmegaEight.Weyl in
theorem certificate3184 : (wChainCheck = true)
    ∧ (reflCheck = true) :=
  ⟨KernelLC.W3184.wChain, KernelLC.W3184.reflCheck_ok⟩

end Certificates
