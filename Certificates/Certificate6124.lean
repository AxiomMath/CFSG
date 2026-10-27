module

public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourActionData
import Certificates.Kernel.Misc.Perm.Fuse.Facts

public section

namespace Certificates

open CertificateChecks

open CFSG.ComponentClassification.PSL3Four in
theorem certificate6124 : Nat.card S = 20160 → ∀ r ∈ [r₂, r₃, r₄], ∀ c ∈ S, c * r = r * c → c * c = 1 →
    ∃ s ∈ S, s * r = r * c * s := KernelMisc.Fuse.facts

end Certificates
