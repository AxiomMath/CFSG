module

public import CFSG.Sporadic.SmallOddCore.J2DataInputs
public meta import Certificates.Data.CFSGNative.SmallOddCore.Check
public meta import CFSG.Sporadic.SmallOddCore.CentData
import Certificates.Kernel.Sporadic.OddCore.J2Cent

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.SmallOddCore Subgroup CFSG.Sporadic.Th.Native in
open CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier in
theorem certificate2279 : (List.range 42).all (fun k => permOK 315 (j2CentTbl k)) = true := KernelSpor.OddCore.j2_permOK_all

end Certificates
