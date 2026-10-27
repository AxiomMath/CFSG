module

public import CFSG.Sporadic.HN.LocalK
import Certificates.Kernel.HNLocal.Facts

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.F5 CFSG.Sporadic.HN.LocalK in
theorem certificate6097 : wG 2 • rootV = rootV ∧ wG 3 • rootV = rootV ∧ Function.Injective hnW ∧
    (∀ k, wG 2 • hnW k = hnW (pi2 k)) ∧ (∀ k, wG 3 • hnW k = hnW (pi3 k)) ∧
    1140000 ≤ Nat.card (MulAction.orbit (J dHN) rootV) := KernelHNLocal.facts6097

end Certificates
