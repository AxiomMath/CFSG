
module

public import CFSG.RankThree.Native.Fi22UCentralizerCheckInputs
import Certificates.Kernel.Fi22U.C8125

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.RankThree CFSG.RankThree.Native CFSG.RankThree.Native.Fi22U CFSG.Monster.B.Fischer
  CFSG.Monster.B.Co2.Native CFSG.Certificates.Native in
theorem certificate8125 :
    rawChainOK 693 ((fi22OuterStrong693 3).extract 0 fi22OuterM693GenCount)
      (fi22OuterStrong693 3) #[0, 1, 3, 9, 45]
      (fi22WordsArr fi22OuterM693GenCount 15 fi22OuterM693Derivations) 4 = true ∧
    rawOrbitSizes 693 (fi22OuterStrong693 3) #[0, 1, 3, 9, 45] = [693, 512, 120, 36, 6] ∧
    (∀ k < 3, siftA 693 (rawLevels 693 (fi22OuterStrong693 2) #[0, 1, 3, 9, 45])
      #[0, 1, 3, 9, 45] 0 (fi22OuterArr693 (64 + k)) = true) ∧
    fi22OuterMPointsNat.Nodup ∧
    (∀ k < 3, ∀ j < 693,
      fi22OuterMPointsNat.getD ((invCand 693 (fi22OuterArr693 0))[
        (fi22OuterArr693 (64 + k))[(fi22OuterArr693 0)[j]!]!]!) 0 =
      (fi22OuterArr3510 (3 + k))[fi22OuterMPointsNat.getD j 0]!) ∧
    (∀ j < 693, (fi22OuterArr3510 1)[fi22OuterMPointsNat.getD j 0]! =
      fi22OuterMPointsNat.getD j 0) ∧
    (∀ i < 4, siftA 3510 (rawLevels 3510 (fi22OuterStrong3510 3) #[0, 1, 2, 6, 4, 3])
      #[0, 1, 2, 6, 4, 3] 0 (fi22OuterArr3510 (147 + i)) = true) ∧
    eqA 3510 (compA 3510 (commA 3510 (fi22OuterArr3510 147) (fi22OuterArr3510 148))
      (commA 3510 (fi22OuterArr3510 149) (fi22OuterArr3510 150))) (fi22OuterArr3510 1) = true := KernelFi22U.C8125.facts8125

end Certificates
