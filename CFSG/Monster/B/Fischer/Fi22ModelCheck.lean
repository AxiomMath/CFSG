
module

public import CFSG.Monster.B.Fischer.Fi22ModelCheckBase

public import CFSG.Monster.B.Fischer.Fi22GraphCheck
public import CFSG.Monster.B.Fischer.Fi22OuterCheck
public import CFSG.Monster.B.Fischer.Fi22OrderCheck
public meta import CFSG.Monster.B.Fischer.Fi22GraphCheck
public meta import CFSG.Monster.B.Fischer.Fi22OuterCheck
public meta import CFSG.Monster.B.Fischer.Fi22OrderCheck
public import Certificates.Certificate3154
public import Certificates.Certificate3154Base

public section

namespace CFSG.Monster.B.Fischer

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

theorem fi22Model_check :
    eqA 3510 fi22GraphOuterArr (idA 3510) = false ∧
    eqA 3510 (compA 3510 fi22GraphOuterArr fi22GraphOuterArr) (idA 3510) = true ∧
    siftA 3510 (rawLevels 3510 fi22StrongArrs fi22BaseArr) fi22BaseArr 0 fi22GraphOuterArr =
      false ∧
    (∀ k < 2, siftA 3510 (rawLevels 3510 fi22StrongArrs fi22BaseArr) fi22BaseArr 0
      (compA 3510 fi22GraphOuterArr (compA 3510 fi22OrigArrs[k]! fi22GraphOuterArr)) = true) ∧
    (∀ p < 3510, p ≠ 0 → ∃ k < 3, ((fi22OuterStrong3510 3)[k]!)[p]! ≠ p) :=
  Certificates.certificate3154

end CFSG.Monster.B.Fischer
