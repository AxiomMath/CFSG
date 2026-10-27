module

public import Certificates.Data.SuzSylowFacts
import Certificates.Kernel.Sporadic.OddCore.Suz1379101L

public section

namespace Certificates

open CertificateChecks

theorem certificate1379101 : CFSG.Sporadic.SuzOddCore.SylowFacts.sylowFactsCheck () = true :=
  KernelSpor.S1379101.check1379101

end Certificates
