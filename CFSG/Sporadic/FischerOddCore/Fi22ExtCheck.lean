
module

public import CFSG.Sporadic.FischerOddCore.Fi22ExtCheckBase

public import CFSG.Sporadic.FischerOddCore.Fi22ExtData
public import CFSG.Monster.B.Fischer.Fi22OuterCheck
public import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public meta import CFSG.Sporadic.FischerOddCore.Fi22ExtData
public meta import CFSG.Monster.B.Fischer.Fi22OuterCheck
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import CFSG.Sporadic.FischerOddCore.Fi22ExtCheckInputs
public import Certificates.Certificate2067

public section

namespace CFSG.Sporadic.FischerOddCore

open CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer

theorem fi22Ext_check :
    layoutOK fi22ExtBytes3510 3 3510 185 = true ∧ layoutOK fi22ExtBytes256 2 256 18 = true ∧
    (∀ L < 185, isInvA 3510 (fi22ExtArr L) (invCand 3510 (fi22ExtArr L)) = true) ∧
    (∀ L < 18, isInvA 256 (fi22ExtArr256 L) (invCand 256 (fi22ExtArr256 L)) = true) ∧
    (∀ x ∈ fi22ExtSmallPointsNat, x < 3510) ∧ fi22ExtSmallPointsNat.Nodup ∧
    fi22ExtSmallPointsNat.length = 256 ∧ (∀ c ∈ fi22ExtGlobalClasses, c < 6) ∧
    fi22ExtGlobalClasses.length = 79 ∧ fi22ExtClassSizes.length = 79 ∧
    wordsOK fi22ExtSmallGenCount 18 fi22ExtSmallDerivations = true :=
  Certificates.certificate2067

end CFSG.Sporadic.FischerOddCore
