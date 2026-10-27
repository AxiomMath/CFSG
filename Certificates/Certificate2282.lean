module

public import CFSG.Sporadic.SmallOddCore.J3DataInputs
public meta import Certificates.Data.CFSGNative.SmallOddCore.Check
public meta import CFSG.Sporadic.SmallOddCore.CentData
import Certificates.Kernel.Sporadic.OddCore.J3Cent

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.SmallOddCore Subgroup CFSG.Sporadic.Th.Native in
open CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier in
theorem certificate2282 : (List.range 31).all (fun k => permOK 6156 (j3CentTbl k)) = true := KernelSpor.OddCore.j3_permOK_all

end Certificates
