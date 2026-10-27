
module


public import Certificates.Data.CFSGNative.Fischer.Polar
import Certificates.Kernel.Misc.Polar

public section

namespace Certificates

open CFSG CFSG.Fischer CFSG.Fischer.Native in
theorem certificate1001 : polarCertificate () = true := CFSG.KD.Misc.Polar.polar_true

end Certificates
