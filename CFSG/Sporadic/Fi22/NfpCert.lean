module

public import Certificates.Data.CFSGNative.Fi22.Nfp
public meta import Certificates.Data.CFSGNative.Fi22.Nfp
public import Certificates.Certificate1010

public section

namespace CFSG.Sporadic.Fi22

open Native

theorem nfp_certificate : nfpCertificate 3 = true :=
  Certificates.certificate1010

end CFSG.Sporadic.Fi22
