module

public import CFSG.Sporadic.SuzRecog.Q3ATitsCheck
import Certificates.Kernel.Sporadic.Q3A.Tits

public section

open CFSG

namespace Certificates

open CertificateChecks

open CFSG in
theorem certificate15089 : CFSG.Sporadic.SuzRecog.Q3A.TitsCheck.titsCheck = true := KernelSpor.Q3AG.titsCheck_true

end Certificates
