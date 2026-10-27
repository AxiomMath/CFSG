module

public import CFSG.CGT.L5R.L2InputsLD
import Certificates.Kernel.M24L2.L5

public section

namespace Certificates

open CertificateChecks

open CFSG.CGT.L5R CFSG.CGT.M24R in
theorem certificate21196 : (bCheckL (mkCtx ()) = true) ∧ (faCheckL (mkCtx ()) = true) ∧
    (fbCheckL (mkCtx ()) (betaT 0) true = true) ∧ (fbCheckL (mkCtx ()) gamT false = true) ∧
    (dCheckL (mkCtx ()) = true) ∧ (wCheckL (mkCtx ()) = true) ∧ (fcCheckL (mkCtx ()) = true) := KernelM24L2.l5_facts

end Certificates
