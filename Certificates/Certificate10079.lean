
module

public import CFSG.Sporadic.Co2Cert.Check
public import Certificates.Data.CFSGNative.Schreier.Refine
public import Certificates.Data.CFSGNative.Schreier.Check
public import Certificates.Data.CFSGNative.Co2Rank3.Orbits
public import Certificates.Data.CFSGNative.Co2Rank3.Data
public import Mathlib.Data.Fintype.Basic
public import CFSG.Sporadic.Co2Rank3.CheckInputsT
import Certificates.Kernel.Sporadic.Co2R3.Final
import Certificates.Kernel.Sporadic.Co2R3.Orbs
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Sporadic.Co2Cert.CheckInputs
import CFSG.Sporadic.Co2Cert.OrderCheckInputs

public section

namespace Certificates

open CFSG.Sporadic.Co2Rank3 in
theorem certificate10079 :
    co2Rank3TOK = true :=
  CertificateChecks.KernelSpor.Co2R3.facts10079

end Certificates
