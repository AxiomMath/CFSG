
module

public import Certificates.Certificate2088Base

public import CFSG.Sporadic.HNOddCore.PCheckInputs
public meta import CFSG.Sporadic.HNOddCore.QCheck
public meta import Std.Data.HashMap
import Certificates.Kernel.Sporadic.OddCore.HN2088

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.HNOddCore CFSG.Sporadic.HNOddCore.Native in
open CFSG.ONSchreier.Native in
theorem certificate2088 : CFSG.Sporadic.HNOddCore.Native.sylowChecks = true :=
  KernelSpor.HN2088.facts2088

end Certificates
