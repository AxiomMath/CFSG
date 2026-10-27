module

public import Certificates.Data.CF67M22
public meta import Certificates.Data.CF67M22
import Certificates.Kernel.SporSch.Mathieu.M22WFacts

public section

namespace Certificates

open CertificateChecks

theorem certificate5192 : Certificates.CF67.M22.m22CF67OK = true :=
  KernelSporSch.M22W.cf67

end Certificates
