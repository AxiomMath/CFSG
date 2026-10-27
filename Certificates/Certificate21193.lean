
module

public import CFSG.CGT.M24R.L2InputsD
import Certificates.Kernel.M24L2.L2
import CFSG.Sporadic.Schreier.MathieuOddCoreWords

public section

namespace Certificates

open CertificateChecks

open CFSG.CGT.M24R in
theorem certificate21193 : (relCheck = true) ∧ (ctxCheck (mkCtx ()) = true) ∧ (tCheck (mkCtx ()) = true) ∧
    (tNormCheck (mkCtx ()) = true) ∧ (bCheck (mkCtx ()) = true) ∧ (faCheck (mkCtx ()) = true) ∧
    (fbCheck (mkCtx ()) = true) ∧ (dCheck (mkCtx ()) = true) ∧ (fcCheck (mkCtx ()) = true) := KernelM24L2.l2_facts

end Certificates
