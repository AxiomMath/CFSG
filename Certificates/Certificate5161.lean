module

public import Certificates.Data.Odd87F3M11
public meta import Certificates.Data.Odd87F3M11
import Certificates.Kernel.SporSch.Mathieu.M11WFacts

public section

namespace Certificates

open CertificateChecks

theorem certificate5161 : Certificates.Odd87F3.M11.m11F3OK = true :=
  KernelSporSch.M11W.f3OK

end Certificates
