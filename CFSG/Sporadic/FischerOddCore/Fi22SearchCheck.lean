module

public import CFSG.Sporadic.FischerOddCore.Fi22RelBoundCheck
public import CFSG.Sporadic.FischerOddCore.Fi22CentOrderCheck
public meta import CFSG.Sporadic.FischerOddCore.Fi22RelBoundCheck
public meta import CFSG.Sporadic.FischerOddCore.Fi22CentOrderCheck
public import CFSG.Sporadic.FischerOddCore.Fi22SearchCheckInputs
public import Certificates.Certificate2071

public section

namespace CFSG.Sporadic.FischerOddCore

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Monster.B.Fischer
open CFSG.Sporadic.FischerOddCore.Native

theorem fi22Search_check :
    searchOK 3510 fi22Nbr (fi22ExtArr 21) fi22SearchBase fi22SearchPoolArr fi22SearchNodes
      fi22SearchAccArr 4 4 = true :=
  Certificates.certificate2071.1

theorem fi22SearchPool_check :
    ∀ j < 64, siftA 3510 (rawLevels 3510 (fi22CentStrong 0) #[0, 1, 2, 3, 6, 4]) #[0, 1, 2, 3, 6, 4]
      0 (fi22CentArr (240 + j)) = true :=
  Certificates.certificate2071.2.1

theorem fi22SearchAcc_check :
    (∀ i < 2, (allLt 3510 fun x =>
      fi22Nbr[(fi22CentArr (304 + i))[x]!]! == imgSorted (fi22CentArr (304 + i)) fi22Nbr[x]!) =
        true ∧
      eqA 3510 (compA 3510 (fi22CentArr (304 + i)) (fi22ExtArr 21))
        (compA 3510 (fi22ExtArr 21) (fi22CentArr (304 + i))) = true) ∧
    fi22InP (fi22CentArr 304) = true ∧ fi22InP (fi22CentArr 305) = false ∧
    fi22InP (compA 3510 fi22GraphOuterArr (fi22CentArr 305)) = true :=
  Certificates.certificate2071.2.2

end CFSG.Sporadic.FischerOddCore
