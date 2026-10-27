module

public import CFSG.Sporadic.Recognition.Fi22MultiplierInputs
public import Certificates.Data.CFSGNative.Bridge.SurjA
import Certificates.Kernel.Fi22Rho.Final

public section

namespace Certificates

open CFSG.Sporadic.Recognition.Fi22Multiplier CFSG.Sporadic.Bridge.TwoGen.Native in
theorem certificate24051 : fi22RelCheck fi22RhoRels = true :=
  CertificateChecks.KernelFi22Rho.rho_check

end Certificates
