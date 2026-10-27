module

public import CFSG.Sporadic.Bridge.SuzMats
import Certificates.Kernel.Sporadic.SuzBridge.Facts

public section

namespace Certificates

open CertificateChecks

theorem certificate9219 : CFSG.Sporadic.Bridge.SuzMats.Facts :=
  KernelSpor.SuzBridge.facts

end Certificates
