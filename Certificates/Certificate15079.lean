module

public import CFSG.Sporadic.SuzRecog.TwistTests
import Certificates.Kernel.Sporadic.OddCore.SuzAB
import Certificates.Kernel.Sporadic.OddCore.SuzFb

public section

open CFSG

namespace Certificates

open CertificateChecks

open CFSG in
theorem certificate15079 : CFSG.Sporadic.SuzRecog.abCheck = true ∧ CFSG.Sporadic.SuzRecog.fibreCheck = true :=
  ⟨KernelSpor.SuzAB.abCheck_true, KernelSpor.SuzFb.fibreCheck_true⟩

end Certificates
