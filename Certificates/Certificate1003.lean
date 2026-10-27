module

import Certificates.Kernel.Misc.Unitary
public import CFSG.Fischer.OrbitBound
public import Certificates.Data.CFSGNative.F4.Unitary

public section

namespace Certificates

open CFSG CFSG.Fischer CFSG.F4.Native in
theorem certificate1003 : uPtsOK = true := CFSG.KD.Misc.Unitary.uPtsOK_true

end Certificates
