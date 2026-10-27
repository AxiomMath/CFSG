
module


public import CFSG.Monster.B.Fischer.Fi22OuterArrays
import Certificates.Kernel.Sporadic.Fi22.C3150
public import CFSG.Monster.B.Fischer.Fi22OrderCheckInputs

public section

namespace Certificates

open CertificateChecks

open CFSG.Certificates.Native CFSG.Monster.B.Fischer CFSG.Monster.B.Co2.Native in
theorem certificate3150 : rawChainOK 3510 ((fi22OuterStrong3510 3).extract 0 fi22OuterMGenCount)
        (fi22OuterStrong3510 3) #[0, 1, 2, 6, 4, 3]
        (fi22WordsArr fi22OuterMGenCount 17 fi22OuterMDerivations) 4 = true ∧
      rawOrbitSizes 3510 (fi22OuterStrong3510 3) #[0, 1, 2, 6, 4, 3] =
        [1, 2816, 567, 320, 18, 2] ∧
      rawChainOK 3510 ((fi22OuterStrong3510 4).extract 0 fi22OuterTGenCount)
        (fi22OuterStrong3510 4) #[0, 1, 2, 3, 6, 4]
        (fi22WordsArr fi22OuterTGenCount 13 fi22OuterTDerivations) 4 = true ∧
      rawOrbitSizes 3510 (fi22OuterStrong3510 4) #[0, 1, 2, 3, 6, 4] = [1024, 32, 4, 1, 1, 1] ∧
      (∀ k < 3, siftA 3510 (rawLevels 3510 fi22StrongArrs fi22BaseArr) fi22BaseArr 0
        (fi22OuterStrong3510 3)[k]! = true) ∧
      (∀ k < 3, ((fi22OuterStrong3510 3)[k]!)[0]! = 0) ∧
      (∀ k < 9, siftA 3510 (rawLevels 3510 fi22StrongArrs fi22BaseArr) fi22BaseArr 0
        (fi22OuterStrong3510 4)[k]! = true) := KernelSpor.Fi22C3150.certificate3150_of

end Certificates
