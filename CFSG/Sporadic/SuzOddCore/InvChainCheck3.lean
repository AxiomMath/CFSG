module

public import CFSG.Sporadic.SuzOddCore.InvArraysCheck
public import Certificates.Data.CFSGNative.Schreier.Check
public meta import CFSG.Sporadic.SuzOddCore.InvArraysCheck
public meta import Certificates.Data.CFSGNative.Schreier.Check
public import Certificates.Certificate2300

public section

namespace CFSG.Sporadic.SuzOddCore

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

theorem invChain_check_3 :
    rawChainOK 1782 (invFullGenArrs 3) (invFullStrongArrs 3) (invFullBases.getD 3 []).toArray
      (invFullDerivs 3) 4 = true ∧
    (rawOrbitSizes 1782 (invFullStrongArrs 3) (invFullBases.getD 3 []).toArray).prod = 2419200 ∧
    rawChainOK 1782 (invInnerGenArrs 3) (invInnerStrongArrs 3)
      (invInnerBases.getD 3 []).toArray (invInnerDerivs 3) 4 = true ∧
    (rawOrbitSizes 1782 (invInnerStrongArrs 3) (invInnerBases.getD 3 []).toArray).prod =
      1209600 :=
  Certificates.certificate2300

end CFSG.Sporadic.SuzOddCore
