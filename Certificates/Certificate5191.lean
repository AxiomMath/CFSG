module

public import Certificates.Data.CF67M12
public meta import Certificates.Data.CF67M12
import Certificates.Kernel.SporSch.Mathieu.M12WFacts

public section

namespace Certificates

open CertificateChecks

theorem certificate5191 : Certificates.CF67.M12.m12CF67OK = true :=
  KernelSporSch.M12W.cf67

end Certificates
