module

public import Certificates.Data.CF67M23
public meta import Certificates.Data.CF67M23
import Certificates.Kernel.SporSch.Mathieu.M23OFacts

public section

namespace Certificates

open CertificateChecks

theorem certificate5193 : Certificates.CF67.M23.m23CF67OK = true :=
  KernelSporSch.M23W.cf67

end Certificates
