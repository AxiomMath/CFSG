
module


public import CFSG.Sporadic.HNOddCore.DCheckInputs
import Certificates.Kernel.Sporadic.OddCore.HND

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.HNOddCore CFSG.Sporadic.HNOddCore.Native in
open CFSG.ONSchreier.Native CFSG.Sporadic.HNOddCore.InvData in
theorem certificate2084 : dataChecks = true := KernelSpor.HND.facts2084

end Certificates
