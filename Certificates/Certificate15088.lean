
module


public import CFSG.Sporadic.SuzRecog.Q3ACheck
import Certificates.Kernel.Sporadic.Q3A.Main

public section

open CFSG

namespace Certificates

open CertificateChecks

open CFSG in
theorem certificate15088 : CFSG.Sporadic.SuzRecog.Q3A.Check.q3aOK = true := KernelSpor.Q3AG.q3aOK_true

end Certificates
