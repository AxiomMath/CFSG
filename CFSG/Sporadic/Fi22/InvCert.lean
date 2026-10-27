
module

public import CFSG.Sporadic.Fi22.InvCertBase

public import Certificates.Data.CFSGNative.Fi22.Inv
public meta import Certificates.Data.CFSGNative.Fi22.Inv
public import Certificates.Certificate1007
public import Certificates.Certificate1007Base

public section

namespace CFSG.Sporadic.Fi22

open Native

theorem inv_certificate : invCertificate 3 = true :=
  Certificates.certificate1007

end CFSG.Sporadic.Fi22
