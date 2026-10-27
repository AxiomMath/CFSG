module

public import CFSG.Sporadic.Schreier.Co3FirstCheckInputs
public meta import CFSG.Sporadic.Schreier.Co3CentralizerCheck
public meta import CFSG.Sporadic.Schreier.Co3Sp6Check
import Certificates.Kernel.Sporadic.Co3.FirstFacts

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Co3 CFSG.Monster.B.Co2.Native in
open CFSG.Certificates.Native CFSG.Sporadic.Schreier.Co3.Native in
theorem certificate2154 : (rawChainOK 276 (co3MCommArrs.extract 0 co3MCommGenCount) co3MCommArrs co3MCommBaseArr
        (wordsArr co3MCommGenCount co3MCommStrongCount co3MCommDerivations) 4 = true ∧
      rawOrbitSizes 276 co3MCommArrs co3MCommBaseArr = [240, 126, 32, 3]
    )
    ∧ (rawChainOK 36 (co3M36Arrs.extract 0 co3M36GenCount) co3M36Arrs co3M36BaseArr
        (wordsArr co3M36GenCount co3M36StrongCount co3M36Derivations) 4 = true ∧
      rawOrbitSizes 36 co3M36Arrs co3M36BaseArr = [36, 35, 18, 8, 4, 2]
    )
    ∧ ((∀ k < 4, eqA 276 co3MCommArrs[k]!
        (commA 276 co3MArrs ((co3MCommPairs.getD k (0, 0)).1 - 1)
          ((co3MCommPairs.getD k (0, 0)).2 - 1)) = true) ∧
      coversOK 36 co3KappaGens (co3M36Arrs.extract 0 6) = true ∧
      (∀ k < 6, siftA 36 co3Sp36Levels co3Sp36BaseArr 0 co3M36Arrs[k]! = true)
    ) := KernelSpor.Co3First.facts

end Certificates
