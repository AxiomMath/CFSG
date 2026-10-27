module

public import CFSG.Sporadic.Schreier.Co3CentralizerCheck
public import CFSG.Sporadic.Schreier.Co3Sp6Check
public meta import CFSG.Sporadic.Schreier.Co3CentralizerCheck
public meta import CFSG.Sporadic.Schreier.Co3Sp6Check
public import CFSG.Sporadic.Schreier.Co3FirstCheckInputs
public import Certificates.Certificate2154

public section

namespace CFSG.Sporadic.Schreier.Co3

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Sporadic.Schreier.Co3.Native

theorem co3MCommChain_check :
    rawChainOK 276 (co3MCommArrs.extract 0 co3MCommGenCount) co3MCommArrs co3MCommBaseArr
      (wordsArr co3MCommGenCount co3MCommStrongCount co3MCommDerivations) 4 = true ∧
    rawOrbitSizes 276 co3MCommArrs co3MCommBaseArr = [240, 126, 32, 3] :=
  Certificates.certificate2154.1

theorem co3M36Chain_check :
    rawChainOK 36 (co3M36Arrs.extract 0 co3M36GenCount) co3M36Arrs co3M36BaseArr
      (wordsArr co3M36GenCount co3M36StrongCount co3M36Derivations) 4 = true ∧
    rawOrbitSizes 36 co3M36Arrs co3M36BaseArr = [36, 35, 18, 8, 4, 2] :=
  Certificates.certificate2154.2.1

theorem co3First_check :
    (∀ k < 4, eqA 276 co3MCommArrs[k]!
      (commA 276 co3MArrs ((co3MCommPairs.getD k (0, 0)).1 - 1)
        ((co3MCommPairs.getD k (0, 0)).2 - 1)) = true) ∧
    coversOK 36 co3KappaGens (co3M36Arrs.extract 0 6) = true ∧
    (∀ k < 6, siftA 36 co3Sp36Levels co3Sp36BaseArr 0 co3M36Arrs[k]! = true) :=
  Certificates.certificate2154.2.2

end CFSG.Sporadic.Schreier.Co3
