module

public import Certificates.Data.Foote82OmegaEight
import Certificates.Kernel.OmegaEight.Bridge919009

public section

namespace Certificates

open CertificateChecks

open CFSG.CGT.Foote82.OmegaEight in
theorem certificate919009 :
    (qLinkCheck () = true)
    ∧ (reflLinkCheck () = true)
    ∧ (transMemCheck () = true)
    ∧ (eichCheck () = true)
    ∧ (typeCheck () = true)
    ∧ (reflRepCheck () = true) := KernelO8.C919009.cert919009

end Certificates
