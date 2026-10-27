module

public import Certificates.Data.CFSGNative.Fi22.Centralizer
public meta import Certificates.Data.CFSGNative.Fi22.Centralizer
public import Certificates.Data.Kernel.Fi22.CentChecks
public import Certificates.Certificate1004

public section

namespace CFSG.Sporadic.Fi22

open Native

theorem cent_certificate :
    centChecksK (orbitData ()) = true :=
  Certificates.certificate1004

end CFSG.Sporadic.Fi22
