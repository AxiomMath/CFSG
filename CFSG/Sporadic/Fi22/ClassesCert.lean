module

public import Certificates.Data.CFSGNative.Fi22.Classes
public meta import Certificates.Data.CFSGNative.Fi22.Classes
public import Certificates.Certificate1006

public section

namespace CFSG.Sporadic.Fi22

open Native

theorem classes_certificate : classesCertificate 3 = true :=
  Certificates.certificate1006

end CFSG.Sporadic.Fi22
