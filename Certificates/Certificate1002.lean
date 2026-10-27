module

public import Certificates.Data.CFSGNative.F4.T46Simple
import Certificates.Kernel.Misc.T46Bridge

public section

namespace Certificates

open CFSG CFSG.F4.Native in
theorem certificate1002 : t46SimpleCertificate () = true := CFSG.KD.Misc.T46.t46Simple

end Certificates
