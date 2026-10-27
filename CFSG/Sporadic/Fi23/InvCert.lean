
module

public import CFSG.Sporadic.Fi23.InvCertBase

public import Certificates.Data.CFSGNative.Fi23.Classes
public import Certificates.Data.CFSGNative.Fi23.Centralizer
public meta import Certificates.Data.CFSGNative.Fi23.Classes
public meta import Certificates.Data.CFSGNative.Fi23.Centralizer
public import CFSG.Sporadic.Fi23.InvCertInputs
public import Certificates.Certificate1014
public import Certificates.Certificate1014Base

public section

namespace CFSG.Sporadic.Fi23.Native

open CFSG.Sporadic.Th.Native CFSG.Perm.Native

set_option compiler.extract_closed false

end CFSG.Sporadic.Fi23.Native

namespace CFSG.Sporadic.Fi23

open Native

theorem inv_certificate : invCertificate 3 = true :=
  Certificates.certificate1014

end CFSG.Sporadic.Fi23
