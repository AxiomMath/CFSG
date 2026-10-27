module

public import CFSG.Sporadic.HNOddCore.SixCheckInputs
public meta import CFSG.Sporadic.HNOddCore.SixData
public meta import CFSG.Sporadic.HNOddCore.SCheck
public meta import CFSG.Sporadic.HNSchreier.PrimCheck
import Certificates.Kernel.Sporadic.OddCore.HN2092

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.HNOddCore CFSG.Sporadic.HNOddCore.Native in
open CFSG.ONSchreier.Native CFSG.Sporadic.HNSchreier.Native CFSG.Monster.B.Co2.Native in
open CFSG.Certificates.Native in
theorem certificate2092 : sixChecks = true :=
  KernelSpor.HN2092.facts2092

end Certificates
