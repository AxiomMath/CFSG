
module

public import CFSG.Sporadic.Fi24.ExtCertBase

public import Certificates.Data.CFSGNative.Fi24.Certificate
public import Certificates.Data.CFSGNative.Fi23.Data
public meta import Certificates.Data.CFSGNative.Fi24.Certificate
public meta import Certificates.Data.CFSGNative.Fi23.Data
public import CFSG.Sporadic.Fi24.ExtCertInputs
public import Certificates.Certificate1018
public import Certificates.Certificate1018Base

public section

namespace CFSG.Sporadic.Fi24.Native

set_option compiler.extract_closed false

end CFSG.Sporadic.Fi24.Native

namespace CFSG.Sporadic.Fi24

open Native

theorem ext_certificate : extChecks () = true :=
  Certificates.certificate1018

end CFSG.Sporadic.Fi24
