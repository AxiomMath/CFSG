
module

public import Certificates.Certificate2151Base

public import CFSG.Sporadic.Schreier.Co3CentralizerCheckInputs
public meta import CFSG.Sporadic.Schreier.Co3SylowCheck
public meta import Certificates.Data.CFSGNative.Schreier.SetOrbit
import Certificates.Kernel.Sporadic.Co3.Centralizer

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Co3 CFSG.Monster.B.Co2.Native in
open CFSG.Certificates.Native CFSG.Sporadic.Schreier.Co3.Native in
theorem certificate2151 : (rawChainOK 276 (co3MArrs.extract 0 co3MGenCount) co3MArrs co3MBaseArr
        (wordsArr co3MGenCount co3MStrongCount co3MDerivations) 4 = true ∧
      rawOrbitSizes 276 co3MArrs co3MBaseArr = [240, 126, 32, 3]
    )
    ∧ (rawChainOK 276 (co3M1Arrs.extract 0 co3M1GenCount) co3M1Arrs co3M1BaseArr
        (wordsArr co3M1GenCount co3M1StrongCount co3M1Derivations) 4 = true ∧
      rawOrbitSizes 276 co3M1Arrs co3M1BaseArr = [132, 72, 10, 2]
    )
    ∧ ((∀ k < 7, siftA 276 co3ChainLevels co3ChainBaseArr 0 co3MArrs[k]! = true ∧
        commutesA 276 co3MArrs[k]! co3ZArr = true) ∧
      (∀ k < 6, siftA 276 co3ChainLevels co3ChainBaseArr 0 co3M1Arrs[k]! = true ∧
        commutesA 276 co3M1Arrs[k]! co3TtArr = true) ∧
      eqA 276 (compA 276 co3TtArr co3TtArr) (idA 276) = true ∧ eqA 276 co3TtArr (idA 276) = false ∧
      siftA 276 co3TLevels co3TBaseArr 0 co3TtArr = true ∧
      siftA 276 co3MLevels co3MBaseArr 0 co3TtArr = true ∧
      fixedList 276 co3ZArr = co3IzNat ∧ fixedList 276 co3TtArr = co3ItNat
    ) := KernelSpor.Co3Cent.facts

end Certificates
