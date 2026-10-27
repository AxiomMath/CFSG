module

public import CFSG.Certificates.CosetTableColumns
public import CFSG.Sporadic.Co2Smith.GlWInputs
import Certificates.Kernel.CosetW.Co2Assembly

public section

namespace Certificates

open CertificateChecks

open CFSG.CosetTable in
theorem certificate21167 :
    (subsetCheckC (restrictWords (subsetOf 7 [0, 1, 2, 3, 4, 5])
      CFSG.Sporadic.Co2Smith.Native.glWRels) [] 100000 1440 = true)
    ∧ (subsetCheckC CFSG.Sporadic.Co2Smith.Native.glWRels [0, 1, 2, 3, 4, 5] 100000 36 = true) := CosetW.proof21167

end Certificates
