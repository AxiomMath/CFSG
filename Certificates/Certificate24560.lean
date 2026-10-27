module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M11Std.HypOneInputs
import Certificates.Kernel.SporSch.Mathieu.M11H1Facts

public section

namespace Certificates

theorem certificate24560 : CFSG.EvenSporadicStandard.M11Std.fourData = true :=
  CertificateChecks.KernelSporSch.M11H1.fourData_eq

end Certificates
