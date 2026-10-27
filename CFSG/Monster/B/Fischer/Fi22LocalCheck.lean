
module

public import CFSG.Monster.B.Fischer.Fi22LocalCheckBase

public import CFSG.Monster.B.Fischer.Fi22OuterCheck
public import CFSG.Monster.B.Fischer.Fi22OrderCheck
public meta import CFSG.Monster.B.Fischer.Fi22OuterCheck
public meta import CFSG.Monster.B.Fischer.Fi22OrderCheck
public import Certificates.Certificate3150
public import Certificates.Certificate3150Base

public section

namespace CFSG.Monster.B.Fischer

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

theorem fi22Local_check :
    rawChainOK 3510 ((fi22OuterStrong3510 3).extract 0 fi22OuterMGenCount)
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
      (fi22OuterStrong3510 4)[k]! = true) :=
  Certificates.certificate3150

end CFSG.Monster.B.Fischer
