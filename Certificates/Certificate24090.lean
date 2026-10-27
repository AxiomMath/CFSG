module

public import CFSG.Sporadic.Recognition.J3MultiplierWords
public import Certificates.Data.CFSGNative.Bridge.SurjA
public import Certificates.Data.CFSGNative.J3.Data
import Certificates.Kernel.J3Mult.Glue24090

public section

namespace Certificates

open CFSG.Sporadic.Recognition.J3Multiplier CFSG.Sporadic.Bridge.TwoGen.Native in
open CFSG.Sporadic.J3.Native (j3Data) in
theorem certificate24090 : j3RelCheck j3Data natWords = true :=
  CertificateChecks.KernelJ3Mult.Glue24090.rel_check

end Certificates
