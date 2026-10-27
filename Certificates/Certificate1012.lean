
module

public import Certificates.Certificate1012Base
import all Certificates.Certificate1012Base

public import Certificates.Data.CFSGNative.Fi23.Certificate
import Certificates.Kernel.Fi23M.Final

public section

namespace Certificates

open CFSG CFSG.Sporadic CFSG.Sporadic.Fi23 CFSG.Sporadic.Fi23.Native in
theorem certificate1012 : fi23Certificate 3 = true := CFSG.KD.Fi23K.fi23_cert

end Certificates
