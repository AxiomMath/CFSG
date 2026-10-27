module

public import CFSG.Sporadic.Presentation.Fi22ExactData
import Certificates.Kernel.Fi22F.Three

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Presentation CFSG.Sporadic.Presentation.Fi22Exact in
open CFSG.CosetTable in
theorem certificate9109 : 6 ∣ orderOf (PresentedGroup.mk {r : FreeGroup (Fin 6) | r ∈ wsF.map FreeGroup.mk}
    (FreeGroup.mk g1w)) := KernelFi22F.six_dvd_orderOf_g1

end Certificates
