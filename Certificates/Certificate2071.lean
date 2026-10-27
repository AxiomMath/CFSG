module

public import CFSG.Sporadic.FischerOddCore.Fi22SearchCheckInputs
public meta import CFSG.Sporadic.FischerOddCore.Fi22RelBoundCheck
public meta import CFSG.Sporadic.FischerOddCore.Fi22CentOrderCheck
import Certificates.Kernel.Sporadic.Fi22.N2071Final
import Certificates.Certificate2065
import Certificates.Certificate2066
import Certificates.Certificate2067
import Certificates.Certificate3039
import Certificates.Certificate3147

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.FischerOddCore CFSG.Monster.B.Co2.Native in
open CFSG.Certificates.Native CFSG.Monster.B.Fischer CFSG.Sporadic.FischerOddCore.Native in
theorem certificate2071 : (searchOK 3510 fi22Nbr (fi22ExtArr 21) fi22SearchBase fi22SearchPoolArr fi22SearchNodes
      fi22SearchAccArr 4 4 = true
    )
    ∧ (∀ j < 64, siftA 3510 (rawLevels 3510 (fi22CentStrong 0) #[0, 1, 2, 3, 6, 4]) #[0, 1, 2, 3, 6, 4]
      0 (fi22CentArr (240 + j)) = true
    )
    ∧ ((∀ i < 2, (allLt 3510 fun x =>
        fi22Nbr[(fi22CentArr (304 + i))[x]!]! == imgSorted (fi22CentArr (304 + i)) fi22Nbr[x]!) =
          true ∧
        eqA 3510 (compA 3510 (fi22CentArr (304 + i)) (fi22ExtArr 21))
          (compA 3510 (fi22ExtArr 21) (fi22CentArr (304 + i))) = true) ∧
      fi22InP (fi22CentArr 304) = true ∧ fi22InP (fi22CentArr 305) = false ∧
      fi22InP (compA 3510 fi22GraphOuterArr (fi22CentArr 305)) = true
    ) := KernelSpor.N2071.facts2071

end Certificates
