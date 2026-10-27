module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
import Certificates.Kernel.Direct.C214002

public section

namespace Certificates

open CertificateChecks

theorem certificate214002 : ∀ s g : alternatingGroup (Fin 6), s ≠ 1 → s ^ 8 = 1 → g * s = s * g → g ^ 8 = 1 :=
  KernelDirect.C214002.alt6_centralizer_pow_eight

end Certificates
