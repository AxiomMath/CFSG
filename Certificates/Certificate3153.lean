
module

public import Certificates.Certificate3153Base
import all Certificates.Certificate3153Base

public import CFSG.Monster.B.Fischer.Fi22GraphBoundCheckInputs
public import Certificates.Data.CFSGNative.FischerOddCore.Checks
import Certificates.Kernel.Sporadic.Fi22.N3153Final

public section

namespace Certificates

open CertificateChecks

open CFSG.Certificates.Native CFSG.Monster.B.Fischer CFSG.Monster.B.Co2.Native in
open CFSG.Sporadic.FischerOddCore.Native in
theorem certificate3153 : adjOK 3510 fi22OrigArrs fi22Nbr fi22N0List = true ∧
      boundsOK 3510 fi22Nbr (idA 3510) fi22GraphBase fi22GraphOrbitBounds 4 = true := KernelSpor.N3153.facts3153

end Certificates
