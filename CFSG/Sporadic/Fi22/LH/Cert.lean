module

public import Certificates.Data.CFSGNative.Fi22.LH
public meta import Certificates.Data.CFSGNative.Fi22.LH
public import Certificates.Certificate1008

public section

namespace CFSG.Sporadic.Fi22

open Native

theorem lh_certificate : lhCertificate () = true :=
  Certificates.certificate1008

end CFSG.Sporadic.Fi22
