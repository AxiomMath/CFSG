module

public import CFSG.Sporadic.Co2Cert.Check
public import CFSG.Monster.B.Mathieu.SylowCore
public import Certificates.Data.CFSGNative.Schreier.Check
public meta import CFSG.Sporadic.Co2Cert.Check
public meta import CFSG.Monster.B.Mathieu.SylowCore
public meta import Certificates.Data.CFSGNative.Schreier.Check
public import CFSG.Sporadic.Co2Cert.OrderCheckInputs
public import Certificates.Certificate3117

public section

namespace CFSG.Sporadic.Co2Cert

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Monster.B.Mathieu

theorem co2Chain_check :
    rawChainOK 2300 co2OrigArrs co2StrongArrs co2BaseArr co2WordArrs 4 = true ∧
    rawOrbitSizes 2300 co2StrongArrs co2BaseArr = [2300, 1408, 567, 192, 30, 4] :=
  Certificates.certificate3117.1

theorem co2cChain_check :
    rawChainOK 2300 co2cOrigArrs co2cStrongArrs co2cBaseArr co2cWordArrs 4 = true ∧
    rawOrbitSizes 2300 co2cStrongArrs co2cBaseArr = [2300, 1408, 567, 192, 30, 4] :=
  Certificates.certificate3117.2.1

theorem co2Conj_check :
    isInvA 2300 co2WArr (invCand 2300 co2WArr) = true ∧
    eqA 2300 co2cOrigArrs[0]! co2OrigArrs[0]! = true ∧
    eqA 2300 co2cOrigArrs[1]!
      (compA 2300 (invCand 2300 co2WArr) (compA 2300 co2OrigArrs[1]! co2WArr)) = true ∧
    eqA 2300 (powArr 2300 co2cOrigArrs[0]! 2) (idA 2300) = true ∧
    eqA 2300 co2cOrigArrs[0]! (idA 2300) = false ∧
    eqA 2300 (powArr 2300 co2cOrigArrs[1]! 5) (idA 2300) = true ∧
    eqA 2300 co2cOrigArrs[1]! (idA 2300) = false ∧
    eqA 2300 (powArr 2300 co2cProdArr 23) (idA 2300) = true ∧
    eqA 2300 co2cProdArr (idA 2300) = false :=
  Certificates.certificate3117.2.2

end CFSG.Sporadic.Co2Cert
