module

public import CFSG.Sporadic.FischerOddCore.Fi22RelBoundCheckInputs
public meta import CFSG.Sporadic.FischerOddCore.Fi22CentCheck
public meta import CFSG.Sporadic.FischerOddCore.Fi22ExtSylowCheck
public meta import CFSG.Monster.B.Fischer.Fi22GraphBoundCheck
public meta import Certificates.Data.CFSGNative.FischerOddCore.Checks
import Certificates.Kernel.Sporadic.Fi22.N2070Final
import Certificates.Certificate3039
import Certificates.Certificate3147

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.FischerOddCore CFSG.Monster.B.Co2.Native in
open CFSG.Certificates.Native CFSG.Monster.B.Fischer CFSG.Sporadic.FischerOddCore.Native in
theorem certificate2070 : ((allLt 3510 fun x =>
        fi22Nbr[fi22GraphOuterArr[x]!]! == imgSorted fi22GraphOuterArr fi22Nbr[x]!) =
        true ∧
      fi22InP (fi22CentArr 79) = false ∧
      fi22InP (compA 3510 fi22GraphOuterArr (fi22CentArr 79)) = true ∧
      eqA 3510 (compA 3510 (fi22CentArr 79) (fi22ExtArr 22))
        (compA 3510 (fi22ExtArr 22) (fi22CentArr 79)) = true ∧
      (∀ c < 4, ∀ x ∈ fi22CentRefPoints.getD c [], x < 3510)
    )
    ∧ (fi22RelBoundOK 1 = true)
    ∧ (fi22RelBoundOK 2 = true)
    ∧ (fi22RelBoundOK 3 = true)
    ∧ (fi22RelBoundOK 4 = true) := KernelSpor.N2070.facts2070

end Certificates
