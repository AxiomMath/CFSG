module

public import Certificates.Data.Odd87F3M23
public meta import Certificates.Data.Odd87F3M23
import Certificates.Kernel.SporSch.Mathieu.M23OFacts

public section

namespace Certificates

open CertificateChecks

theorem certificate5162 : Certificates.Odd87F3.M23.m23F3OK = true :=
  KernelSporSch.M23W.f3OK

end Certificates
