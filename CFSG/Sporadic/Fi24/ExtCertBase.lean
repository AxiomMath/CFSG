
module

public import Certificates.Data.CFSGNative.Fi24.Certificate
public import Certificates.Data.CFSGNative.Fi23.Data
public meta import Certificates.Data.CFSGNative.Fi24.Certificate
public meta import Certificates.Data.CFSGNative.Fi23.Data
public import CFSG.Sporadic.Fi24.ExtCertInputs

@[expose] public section

namespace CFSG.Sporadic.Fi24.Native

set_option compiler.extract_closed false

end CFSG.Sporadic.Fi24.Native

namespace CFSG.Sporadic.Fi24

open Native

end CFSG.Sporadic.Fi24
