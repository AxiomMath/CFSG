module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.Fi22TwoBQCheck
import Certificates.Kernel.Sporadic.Fi22.Q450106

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.Fi22TwoB in
theorem certificate450106 : checkQ () = true :=
  KernelSpor.Q450106.check

end Certificates
