module

public import CFSG.Sporadic.SuzOddCore.SylowCheckInputs
public meta import CFSG.Sporadic.SuzOddCore.InvTCheck
public meta import Certificates.Data.CFSGNative.PSL3Four.Basic
import Certificates.Kernel.Sporadic.OddCore.S2307
import Certificates.Kernel.Sporadic.OddCore.S2307Neg

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.SuzOddCore CFSG.Monster.B.Co2.Native CFSG.Certificates.Native in
open CFSG.PSL3Four.Native in
theorem certificate2307 : sylowChecks sylowEnum fusionEnums = true :=
  KernelSpor.S2307.facts2307

end Certificates
