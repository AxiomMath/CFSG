module

public import CFSG.Sporadic.FischerOddCore.Fi22CentCheck
public import CFSG.Sporadic.FischerOddCore.Fi22ExtSylowCheck
public import CFSG.Monster.B.Fischer.Fi22GraphBoundCheck
public import Certificates.Data.CFSGNative.FischerOddCore.Checks
public meta import CFSG.Sporadic.FischerOddCore.Fi22CentCheck
public meta import CFSG.Sporadic.FischerOddCore.Fi22ExtSylowCheck
public meta import CFSG.Monster.B.Fischer.Fi22GraphBoundCheck
public meta import Certificates.Data.CFSGNative.FischerOddCore.Checks
public import CFSG.Sporadic.FischerOddCore.Fi22RelBoundCheckInputs
public import Certificates.Certificate2070

public section

namespace CFSG.Sporadic.FischerOddCore

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Monster.B.Fischer
open CFSG.Sporadic.FischerOddCore.Native

theorem fi22RelBound_check :
    (allLt 3510 fun x =>
      fi22Nbr[fi22GraphOuterArr[x]!]! == imgSorted fi22GraphOuterArr fi22Nbr[x]!) =
      true ∧
    fi22InP (fi22CentArr 79) = false ∧
    fi22InP (compA 3510 fi22GraphOuterArr (fi22CentArr 79)) = true ∧
    eqA 3510 (compA 3510 (fi22CentArr 79) (fi22ExtArr 22))
      (compA 3510 (fi22ExtArr 22) (fi22CentArr 79)) = true ∧
    (∀ c < 4, ∀ x ∈ fi22CentRefPoints.getD c [], x < 3510) :=
  Certificates.certificate2070.1

theorem fi22RelBound_check1 : fi22RelBoundOK 1 = true :=
  Certificates.certificate2070.2.1

theorem fi22RelBound_check2 : fi22RelBoundOK 2 = true :=
  Certificates.certificate2070.2.2.1

theorem fi22RelBound_check3 : fi22RelBoundOK 3 = true :=
  Certificates.certificate2070.2.2.2.1

theorem fi22RelBound_check4 : fi22RelBoundOK 4 = true :=
  Certificates.certificate2070.2.2.2.2

end CFSG.Sporadic.FischerOddCore
