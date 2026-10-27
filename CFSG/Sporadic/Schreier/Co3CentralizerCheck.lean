
module

public import CFSG.Sporadic.Schreier.Co3CentralizerCheckBase

public import CFSG.Sporadic.Schreier.Co3SylowCheck
public import Certificates.Data.CFSGNative.Schreier.SetOrbit
public meta import CFSG.Sporadic.Schreier.Co3SylowCheck
public meta import Certificates.Data.CFSGNative.Schreier.SetOrbit
public import CFSG.Sporadic.Schreier.Co3CentralizerCheckInputs
public import Certificates.Certificate2151

public section

namespace CFSG.Sporadic.Schreier.Co3

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Sporadic.Schreier.Co3.Native

theorem co3MChain_check :
    rawChainOK 276 (co3MArrs.extract 0 co3MGenCount) co3MArrs co3MBaseArr
      (wordsArr co3MGenCount co3MStrongCount co3MDerivations) 4 = true ∧
    rawOrbitSizes 276 co3MArrs co3MBaseArr = [240, 126, 32, 3] :=
  Certificates.certificate2151.1

theorem co3M1Chain_check :
    rawChainOK 276 (co3M1Arrs.extract 0 co3M1GenCount) co3M1Arrs co3M1BaseArr
      (wordsArr co3M1GenCount co3M1StrongCount co3M1Derivations) 4 = true ∧
    rawOrbitSizes 276 co3M1Arrs co3M1BaseArr = [132, 72, 10, 2] :=
  Certificates.certificate2151.2.1

theorem co3Centralizer_check :
    (∀ k < 7, siftA 276 co3ChainLevels co3ChainBaseArr 0 co3MArrs[k]! = true ∧
      commutesA 276 co3MArrs[k]! co3ZArr = true) ∧
    (∀ k < 6, siftA 276 co3ChainLevels co3ChainBaseArr 0 co3M1Arrs[k]! = true ∧
      commutesA 276 co3M1Arrs[k]! co3TtArr = true) ∧
    eqA 276 (compA 276 co3TtArr co3TtArr) (idA 276) = true ∧ eqA 276 co3TtArr (idA 276) = false ∧
    siftA 276 co3TLevels co3TBaseArr 0 co3TtArr = true ∧
    siftA 276 co3MLevels co3MBaseArr 0 co3TtArr = true ∧
    fixedList 276 co3ZArr = co3IzNat ∧ fixedList 276 co3TtArr = co3ItNat :=
  Certificates.certificate2151.2.2

end CFSG.Sporadic.Schreier.Co3
