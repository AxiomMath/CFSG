module

public import Certificates.Data.CF67M11
public meta import Certificates.Data.CF67M11
import Certificates.Kernel.SporSch.Mathieu.M11WFacts

public section

namespace Certificates

open CertificateChecks

theorem certificate5190 : Certificates.CF67.M11.m11CF67OK = true :=
  KernelSporSch.M11W.cf67

end Certificates
