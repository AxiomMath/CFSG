
module

public import CFSG.Sporadic.FischerOddCore.Fi22ExtSylowCheckBase

public import CFSG.Sporadic.FischerOddCore.Fi22ExtCheck
public import CFSG.Monster.B.Fischer.Fi22CoverCheckBase
public import CFSG.Monster.B.Fischer.Fi22OrderCheck
public import CFSG.Monster.B.Fischer.Fi22GraphCheck
public meta import CFSG.Sporadic.FischerOddCore.Fi22ExtCheck
public meta import CFSG.Monster.B.Fischer.Fi22CoverCheckBase
public meta import CFSG.Monster.B.Fischer.Fi22OrderCheck
public meta import CFSG.Monster.B.Fischer.Fi22GraphCheck
public import CFSG.Sporadic.FischerOddCore.Fi22ExtSylowCheckInputs
public import Certificates.Certificate2069

public section

namespace CFSG.Sporadic.FischerOddCore

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Monster.B.Fischer

theorem fi22ExtSylow_check :
    fi22InP (fi22ExtArr 0) = true ∧ fi22InP (fi22ExtArr 1) = false ∧
    fi22InP (compA 3510 fi22GraphOuterArr (fi22ExtArr 1)) = true ∧
    (∀ k < 9, eqA 3510 (compA 3510 (fi22ExtArr (2 + k)) (fi22ExtArr 0))
      (compA 3510 (fi22ExtArr 0) (fi22OuterStrong3510 4)[k]!) = true) ∧
    (∀ k < 9, eqA 3510 (fi22ExtArr (11 + k)) (fi22ExtArr (2 + k)) = true) ∧
    eqA 3510 (fi22ExtArr 20) (fi22ExtArr 1) = true ∧
    fi22InT (compA 3510 fi22ExtQiArr
      (compA 3510 (fi22ExtArr 1) (compA 3510 (fi22ExtArr 1) (fi22ExtArr 0)))) = true ∧
    (∀ k < 9, fi22InT (compA 3510 fi22ExtQiArr (compA 3510 (fi22ExtArr 1)
      (compA 3510 (fi22ExtArr (2 + k)) (compA 3510 fi22ExtViArr (fi22ExtArr 0))))) = true) ∧
    (∀ k < 10, ∀ i < 256, (fi22ExtArr256 k)[i]! < 256 ∧
      fi22ExtDArr[(fi22ExtArr256 k)[i]!]! = (fi22ExtArr (11 + k))[fi22ExtDArr[i]!]!) ∧
    (∀ i < 256, fi22ExtPosArr[fi22ExtDArr[i]!]! = i) ∧
    rawChainOK 256 (fi22ExtSmallStrong.extract 0 10) fi22ExtSmallStrong #[0, 1, 2, 3, 4, 6]
      (fi22WordsArr 10 18 fi22ExtSmallDerivations) 4 = true ∧
    rawOrbitSizes 256 fi22ExtSmallStrong #[0, 1, 2, 3, 4, 6] = [256, 64, 4, 2, 2, 1] :=
  Certificates.certificate2069

end CFSG.Sporadic.FischerOddCore
