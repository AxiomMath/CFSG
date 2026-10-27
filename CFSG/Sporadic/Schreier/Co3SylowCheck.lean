module

public import CFSG.Sporadic.Schreier.Co3Outer
public import CFSG.Sporadic.Schreier.Co3OrderCheck
public meta import CFSG.Sporadic.Schreier.Co3Outer
public meta import CFSG.Sporadic.Schreier.Co3OrderCheck
public import CFSG.Sporadic.Schreier.Co3SylowCheckInputs
public import Certificates.Certificate2162

public section

namespace CFSG.Sporadic.Schreier.Co3

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Sporadic.Schreier.Co3.Native

theorem co3TChain_check :
    rawChainOK 276 (co3TArrs.extract 0 co3TGenCount) co3TArrs co3TBaseArr
      (wordsArr co3TGenCount co3TStrongCount co3TDerivations) 4 = true ∧
    rawOrbitSizes 276 co3TArrs co3TBaseArr = [128, 4, 2] :=
  Certificates.certificate2162.1

theorem co3TSift_check :
    (∀ k < 8, siftA 276 co3ChainLevels co3ChainBaseArr 0 co3TArrs[k]! = true) ∧
    siftA 276 co3ChainLevels co3ChainBaseArr 0 co3ZArr = true ∧
    siftA 276 co3TLevels co3TBaseArr 0 co3ZArr = true ∧
    (∀ k < 8, commutesA 276 co3ZArr co3TArrs[k]! = true) ∧
    eqA 276 (compA 276 co3ZArr co3ZArr) (idA 276) = true ∧ eqA 276 co3ZArr (idA 276) = false ∧
    centerCheck3 276 co3TLevels (co3TArrs.extract 0 8) co3ZArr = true :=
  Certificates.certificate2162.2

end CFSG.Sporadic.Schreier.Co3
