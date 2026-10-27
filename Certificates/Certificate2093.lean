
module

public import Certificates.Certificate2093Base

public import CFSG.Sporadic.HNOddCore.WCheckInputs
public meta import CFSG.Sporadic.HNOddCore.PCheckBase
import Certificates.Kernel.Sporadic.OddCore.HN2093

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.HNOddCore CFSG.Sporadic.HNOddCore.Native in
open CFSG.ONSchreier.Native in
theorem certificate2093 : witCoverChecks = true := KernelSpor.HN2093.facts2093

end Certificates
