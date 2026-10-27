
module

public import Certificates.Certificate2053Base

public import CFSG.Sporadic.Co2Schreier.KerCheckInputs
public meta import CFSG.Sporadic.Co2Schreier.WitCheck
public meta import CFSG.Sporadic.Co2Schreier.CoreCheckBase
import Certificates.Kernel.SporSch.Co2M.KerP

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Co2Schreier CFSG.Monster.B.Co2.Native CFSG.Certificates.Native in
open CFSG.Monster.B.Mathieu CFSG.Sporadic.Co2Cert in
theorem certificate2053 : kerCheck kerData = true := KernelSporSch.Co2M.ker_check

end Certificates
