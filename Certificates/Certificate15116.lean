module

public import CFSG.Sporadic.SuzRecog.LevelTwoCoverWCheck
import Certificates.Kernel.Sporadic.OddCore.SuzWF

public section

open CFSG

namespace Certificates

open CFSG in
theorem certificate15116 : CFSG.Sporadic.SuzRecog.LevelTwo.WCheck.wOK = true :=
  CertificateChecks.KernelSpor.SuzWF.facts15116

end Certificates
