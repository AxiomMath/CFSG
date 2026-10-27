module

public import Std.Data.HashMap
public import CFSG.Sporadic.Schreier.TitsCentralCheck
public import CFSG.Quasithin.Recognition.CertTitsJCheck
public import CFSG.Quasithin.Recognition.CertVertexTable2
public import CFSG.Quasithin.Recognition.CertDataTitsOuter
public meta import Std.Data.HashMap
public meta import CFSG.Sporadic.Schreier.TitsData
public meta import CFSG.Sporadic.Schreier.TitsArrays
public meta import CFSG.Sporadic.Schreier.TitsBasic
public meta import CFSG.Sporadic.Schreier.TitsCertCheck
public meta import CFSG.Sporadic.Schreier.TitsLocalCheck
public meta import CFSG.Sporadic.Schreier.TitsActionCheck
public meta import CFSG.Sporadic.Schreier.TitsOrbit
public meta import CFSG.Sporadic.Schreier.TitsStabCheck
public meta import CFSG.Sporadic.Schreier.TitsEnum
public meta import CFSG.Sporadic.Schreier.TitsCentralCheck
public meta import Certificates.Data.CFSGNative.Schreier.Check
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Data
public meta import CFSG.Quasithin.Recognition.CertTitsEnum4
public meta import CFSG.Quasithin.Recognition.CertVertexTable
public meta import CFSG.Quasithin.Recognition.CertVertexTable2
public meta import CFSG.Quasithin.Recognition.CertTitsJCheck
public meta import CFSG.Quasithin.Recognition.CertDataTitsOuter
public import CFSG.Quasithin.Recognition.CertTwoF4CheckInputs
public import Certificates.Certificate8079

public section

namespace CFSG.Quasithin

open CFSG.Certificates.Native CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.Tits

theorem pModel_check :
    pPel.size = 1024 ∧
    (allLt 1024 fun i => allLt 1024 fun j => decide ((pMulT[i]!)[j]! < 1024) &&
      titsJBase.all fun p => (pPel[(pMulT[i]!)[j]!]!)[p]! == (pPel[i]!)[(pPel[j]!)[p]!]!) = true ∧
    (allLt 1024 fun i => decide (pInvT[i]! < 1024) &&
      isInvA 1755 pPel[i]! (invCand 1755 pPel[i]!) &&
      eqA 1755 (invCand 1755 pPel[i]!) pPel[pInvT[i]!]!) = true ∧
    pOneI < 1024 ∧ eqA 1755 pPel[pOneI]! (idA 1755) = true ∧
    pZI < 1024 ∧ eqA 1755 pPel[pZI]! jZArr = true ∧
    (allLt 1024 fun i => allLt 1024 fun j => i == j ||
      titsJBase.any fun p => (pPel[i]!)[p]! != (pPel[j]!)[p]!) = true ∧
    (allLt 4 fun k => isInvA 1755 pGenArrs[k]! pGenInvArrs[k]!) = true ∧
    (allLt 4 fun k => allLt 1024 fun i => decide ((pCjT[k]!)[i]! < 1024) &&
      eqA 1755 (compA 1755 (compA 1755 pGenArrs[k]! pPel[i]!) pGenInvArrs[k]!)
        pPel[(pCjT[k]!)[i]!]!) = true ∧
    (allLt 1024 fun i => decide (pCcT[i]! < 1024) &&
      eqA 1755 (compA 1755 (compA 1755 jCArr pPel[i]!) jCInv) pPel[pCcT[i]!]!) = true ∧
    VConds2 pOps pEB pFB pRB pCc pCj pI0 pWtab :=
  Certificates.certificate8079.1

theorem twoF4Pi_check :
    isInvA 1755 titsPiArr piInv = true ∧
    (titsSWords.all fun w => siftA 1755 titsSLevels (baseArr 1755 titsSBase) 0
      (conjPi (wordArr 1755 titsDerivedArrs w))) = true ∧
    (titsHWords.all fun w => siftA 1755 titsHLevels (baseArr 1755 titsHBase) 0
      (conjPi (wordArr 1755 titsDerivedArrs w))) = true ∧
    (titsNWords.all fun w => siftA 1755 titsNLevels (baseArr 1755 titsNBase) 0
      (conjPi (wordArr 1755 titsDerivedArrs w))) = true ∧
    (titsJWords.all fun w => siftA 1755 titsJLevels (baseArr 1755 titsJBase) 0
      (conjPi (wordArr 1755 titsDerivedArrs w))) = true ∧
    (titsKWords.all fun w => siftA 1755 titsKLevels (baseArr 1755 titsKBase) 0
      (conjPi (wordArr 1755 titsDerivedArrs w))) = true ∧
    siftA 1755 titsJLevels (baseArr 1755 titsJBase) 0 (compA 1755 titsPiArr titsPiArr) = true ∧
    (allLt 3 fun k => siftA 1755 titsJLevels (baseArr 1755 titsJBase) 0
      (compA 1755 (compA 1755 (compA 1755 jGenArrs[k]! titsPiArr) jGenInvArrs[k]!) piInv)) = true ∧
    all5 1755 titsSLevels (fun a => !(commutesAll 1755 (compA 1755 a titsPiArr)
      (titsSArrs.extract 0 3))) = true ∧
    eqA 1755 (compA 1755 (compA 1755 titsPiArr jZArr) piInv) jZArr = true ∧
    (allLt 512 fun i => !(titsJBase.all fun p => (jPel[i]!)[titsPiArr[p]!]! == p)) = true :=
  Certificates.certificate8079.2

end CFSG.Quasithin
