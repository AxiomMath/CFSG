module

public import Certificates.Data.Odd87F3M12
public meta import Certificates.Data.Odd87F3M12
import Certificates.Kernel.SporSch.Mathieu.M12DWFacts

public section

namespace Certificates

open CertificateChecks

theorem certificate5164 : Certificates.Odd87F3.M12.m12F3OK = true :=
  KernelSporSch.M12DW.f3OK

end Certificates
