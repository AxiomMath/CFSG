module

public import CFSG.Sporadic.HNOddCore.QCheckInputs
import Certificates.Kernel.Sporadic.OddCore.HN2089

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.HNOddCore CFSG.Sporadic.HNOddCore.Native in
open CFSG.ONSchreier.Native in
theorem certificate2089 : qChecks = true :=
  KernelSpor.HN2089.facts2089

end Certificates
