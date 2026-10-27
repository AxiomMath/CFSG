module

public import Certificates.Data.Odd87F3M22
public meta import Certificates.Data.Odd87F3M22
import Certificates.Kernel.SporSch.Mathieu.M22WFacts

public section

namespace Certificates

open CertificateChecks

theorem certificate5163 : Certificates.Odd87F3.M22.m22F3OK = true :=
  KernelSporSch.M22W.f3OK

end Certificates
