module

public import Certificates.Data.GH74.BTFinCkM12
public meta import Certificates.Data.GH74.BTFinCkM12
import Certificates.Kernel.SporSch.Mathieu.M12OddFacts

public section

namespace Certificates

open CertificateChecks

theorem certificate55101 : Certificates.BTFinCk.M12.m12OddCk = true := KernelSporSch.M12Odd.m12OddCk_eq

end Certificates
