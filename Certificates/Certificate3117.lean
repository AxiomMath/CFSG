module

public import CFSG.Sporadic.Co2Cert.OrderCheckInputs
import Certificates.Kernel.Sporadic.Co2.Order

public section

namespace Certificates

open CertificateChecks

open CFSG.Certificates.Native CFSG.Sporadic.Co2Cert CFSG.Monster.B.Co2.Native CFSG.Monster.B.Mathieu in
theorem certificate3117 : (rawChainOK 2300 co2OrigArrs co2StrongArrs co2BaseArr co2WordArrs 4 = true ∧
       rawOrbitSizes 2300 co2StrongArrs co2BaseArr = [2300, 1408, 567, 192, 30, 4])
    ∧ (rawChainOK 2300 co2cOrigArrs co2cStrongArrs co2cBaseArr co2cWordArrs 4 = true ∧
       rawOrbitSizes 2300 co2cStrongArrs co2cBaseArr = [2300, 1408, 567, 192, 30, 4])
    ∧ (isInvA 2300 co2WArr (invCand 2300 co2WArr) = true ∧
       eqA 2300 co2cOrigArrs[0]! co2OrigArrs[0]! = true ∧
       eqA 2300 co2cOrigArrs[1]!
         (compA 2300 (invCand 2300 co2WArr) (compA 2300 co2OrigArrs[1]! co2WArr)) = true ∧
       eqA 2300 (powArr 2300 co2cOrigArrs[0]! 2) (idA 2300) = true ∧
       eqA 2300 co2cOrigArrs[0]! (idA 2300) = false ∧
       eqA 2300 (powArr 2300 co2cOrigArrs[1]! 5) (idA 2300) = true ∧
       eqA 2300 co2cOrigArrs[1]! (idA 2300) = false ∧
       eqA 2300 (powArr 2300 co2cProdArr 23) (idA 2300) = true ∧
       eqA 2300 co2cProdArr (idA 2300) = false) := KernelSpor.Co2Order.facts

end Certificates
