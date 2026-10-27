module

public import CFSG.CGT.L5R.R3Inputs
import Certificates.Kernel.M24L2.R3

public section

namespace Certificates

open CertificateChecks

open CFSG.CGT.L5R.R3 CFSG.CGT.M24R in
theorem certificate21197 : identCheck = true ∧ centCheck (mkCtx ()) = true := KernelM24L2.r3_facts

end Certificates
