
module

public import CFSG.Monster.B.Fischer.Fi22OuterCheckBase

public import CFSG.Monster.B.Fischer.Fi22OuterArrays
public import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public meta import CFSG.Monster.B.Fischer.Fi22OuterArrays
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import CFSG.Monster.B.Fischer.Fi22OuterCheckInputs
public import Certificates.Certificate3038
public import Certificates.Certificate3038Base

public section

namespace CFSG.Monster.B.Fischer

open CFSG.Monster.B.Co2.Native

theorem fi22Outer_check :
    layoutOK fi22Outer3510Bytes 3 3510 151 = true ∧ layoutOK fi22Outer693Bytes 3 693 104 = true ∧
    layoutOK fi22Outer256Bytes 2 256 16 = true ∧
    (∀ L < 151, isInvA 3510 (fi22OuterArr3510 L) (invCand 3510 (fi22OuterArr3510 L)) = true) ∧
    (∀ L < 104, isInvA 693 (fi22OuterArr693 L) (invCand 693 (fi22OuterArr693 L)) = true) ∧
    (∀ L < 16, isInvA 256 (fi22OuterArr256 L) (invCand 256 (fi22OuterArr256 L)) = true) ∧
    (∀ x ∈ fi22OuterMPointsNat, x < 3510) ∧ (∀ x ∈ fi22OuterTPointsNat, x < 3510) ∧
    (∀ r < 3, ∀ x ∈ fi22OuterWitnessOrbitNat r, x < 693) ∧
    ((List.range 3).map fun r => (fi22OuterWitnessOrbitNat r).length) = [512, 180, 1] ∧
    fi22OuterUnitaryPoints.length = 693 * 6 ∧ fi22OuterTransvectionVectors.length = 46 * 6 ∧
    (∀ k < 693 * 6, codeAt fi22OuterUnitaryPoints k < 4) ∧
    (∀ k < 46 * 6, codeAt fi22OuterTransvectionVectors k < 4) ∧
    wordsOK fi22OuterMGenCount 17 fi22OuterMDerivations = true ∧
    wordsOK fi22OuterTGenCount 13 fi22OuterTDerivations = true ∧
    wordsOK fi22OuterT256GenCount 16 fi22OuterT256Derivations = true ∧
    wordsOK fi22OuterUnitaryGenCount 49 fi22OuterUnitaryDerivations = true ∧
    wordsOK fi22OuterM693GenCount 15 fi22OuterM693Derivations = true ∧
    wordsOK fi22OuterMComm693GenCount 14 fi22OuterMComm693Derivations = true ∧
    wordsOK fi22OuterD693GenCount 11 fi22OuterD693Derivations = true :=
  Certificates.certificate3038

end CFSG.Monster.B.Fischer
