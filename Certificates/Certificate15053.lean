module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Step18SuzCenterTests
import Certificates.Kernel.Sporadic.OddCore.SuzCentre

public section

namespace Certificates

open CertificateChecks

open CFSG in
theorem certificate15053 : CFSG.ComponentClassification.AS81.SuzCenter.suzSylowCenterCheck = true :=
  KernelSpor.SuzCentre.suzSylowCenterCheck_true

end Certificates
