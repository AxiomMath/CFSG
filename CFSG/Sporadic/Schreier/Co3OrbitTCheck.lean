module

public import CFSG.Sporadic.Schreier.Co3OrbitZCheck
public meta import CFSG.Sporadic.Schreier.Co3OrbitZCheck
public import CFSG.Sporadic.Schreier.Co3OrbitTCheckInputs
public import CFSG.Sporadic.Schreier.Co3StabItInputs
public meta import CFSG.Sporadic.Schreier.Co3StabItInputs
public import Certificates.Certificate2156

public section

namespace CFSG.Sporadic.Schreier.Co3

open CFSG.Certificates.Native CFSG.Sporadic.Schreier.Co3.Native CFSG.Monster.B.Co2.Native

theorem co3OrbitT_check :
    rawChainOK 276 (co3StabItArrs.extract 0 8) co3StabItArrs co3StabItBaseArr
      (wordsArr 8 8 co3StabItDerivations) 4 = true ∧
    rawOrbitSizes 276 co3StabItArrs co3StabItBaseArr = [276, 275, 162, 105, 64, 3, 2] ∧
    (∀ j < 8, siftA 276 co3ChainLevels co3ChainBaseArr 0 co3StabItArrs[j]! = true) ∧
    (∀ k < 3, (co3StabItLevels[5]!).pts[k]! ∈ co3ItNat → k = 0) :=
  Certificates.certificate2156

end CFSG.Sporadic.Schreier.Co3
