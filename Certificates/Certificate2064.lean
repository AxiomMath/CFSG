module

public import CFSG.Sporadic.FischerOddCore.Fi22CTICheckInputs
public meta import CFSG.Sporadic.FischerOddCore.Fi22SylowCheck
import Certificates.Kernel.Sporadic.Fi22.G2064
import Certificates.Certificate2065
import Certificates.Certificate2066
import Certificates.Certificate2067
import Certificates.Certificate3039
import Certificates.Certificate3147

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.FischerOddCore CFSG.Monster.B.Co2.Native in
open CFSG.Certificates.Native CFSG.Monster.B.Fischer CFSG.Sporadic.FischerOddCore.Native in
theorem certificate2064 : ctiChecks = true :=
  KernelSpor.Fi22CtiG.checks

end Certificates
