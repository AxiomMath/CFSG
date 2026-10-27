module

public import CFSG.Sporadic.FischerOddCore.Fi22CentData
public import CFSG.Monster.B.Fischer.Fi22OuterCheck
public import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public meta import CFSG.Sporadic.FischerOddCore.Fi22CentData
public meta import CFSG.Monster.B.Fischer.Fi22OuterCheck
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import CFSG.Sporadic.FischerOddCore.Fi22CentCheckInputs
public import Certificates.Certificate2065

public section

namespace CFSG.Sporadic.FischerOddCore

open CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer

theorem fi22Cent_check :
    layoutOK fi22CentBytes 3 3510 306 = true ∧
    (∀ L < 306, isInvA 3510 (fi22CentArr L) (invCand 3510 (fi22CentArr L)) = true) ∧
    fi22CentBases = List.replicate 5 [0, 1, 2, 3, 6, 4] ∧
    fi22CentStrongStart = [0, 19, 35, 44, 63] ∧ fi22CentStrongCount = [19, 16, 9, 19, 16] ∧
    fi22CentGenCount = [12, 9, 3, 9, 9] ∧
    (∀ c < 5, wordsOK (fi22CentGenCount.getD c 0) (fi22CentStrongCount.getD c 0)
      (fi22CentDerivations.getD c []) = true) ∧
    fi22CentSylows.length = 11 ∧ fi22CentWitnesses.length = 66 ∧
    fi22SearchNodeDataOK = true ∧ fi22SearchBase.length = 10 ∧
    (∀ x ∈ fi22SearchBase, x < 3510) :=
  Certificates.certificate2065

end CFSG.Sporadic.FischerOddCore
