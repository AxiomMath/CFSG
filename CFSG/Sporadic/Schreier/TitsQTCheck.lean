module

public import CFSG.Sporadic.Schreier.TitsCentralCheck
public meta import CFSG.Sporadic.Schreier.TitsData
public meta import CFSG.Sporadic.Schreier.TitsArrays
public meta import CFSG.Sporadic.Schreier.TitsBasic
public meta import CFSG.Sporadic.Schreier.TitsCertCheck
public meta import CFSG.Sporadic.Schreier.TitsLocalCheck
public meta import CFSG.Sporadic.Schreier.TitsEnum
public meta import CFSG.Sporadic.Schreier.TitsCentralCheck
public meta import Certificates.Data.CFSGNative.Schreier.Check
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Data
public import CFSG.Sporadic.Schreier.TitsQTCheckInputs
public import Certificates.Certificate4155

public section

namespace CFSG.Sporadic.Schreier.TitsQT

open CFSG.Sporadic.Schreier.Tits CFSG.Certificates.Native CFSG.Monster.B.Co2.Native

theorem titsQT_check :
    siftA 1755 titsSLevels (baseArr 1755 titsSBase) 0 conjXArr = true ∧
    siftA 1755 titsSLevels (baseArr 1755 titsSBase) 0 conjYArr = true ∧
    (compA 1755 conjXArr conjYArr)[12]! = 115 ∧
    (compA 1755 conjYArr conjXArr)[12]! = 117 :=
  Certificates.certificate4155

end CFSG.Sporadic.Schreier.TitsQT
