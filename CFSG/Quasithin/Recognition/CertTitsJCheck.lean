
module

public import CFSG.Quasithin.Recognition.CertTitsJCheckBase

public import Std.Data.HashMap
public import CFSG.Sporadic.Schreier.TitsStabCheck
public import CFSG.Quasithin.Recognition.CertTitsEnum4
public import CFSG.Quasithin.Recognition.CertVertexTable
public meta import Std.Data.HashMap
public meta import CFSG.Sporadic.Schreier.TitsData
public meta import CFSG.Sporadic.Schreier.TitsArrays
public meta import CFSG.Sporadic.Schreier.TitsBasic
public meta import CFSG.Sporadic.Schreier.TitsCertCheck
public meta import CFSG.Sporadic.Schreier.TitsLocalCheck
public meta import CFSG.Sporadic.Schreier.TitsActionCheck
public meta import CFSG.Sporadic.Schreier.TitsOrbit
public meta import CFSG.Sporadic.Schreier.TitsStabCheck
public meta import Certificates.Data.CFSGNative.Schreier.Check
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Data
public meta import CFSG.Quasithin.Recognition.CertTitsEnum4
public meta import CFSG.Quasithin.Recognition.CertVertexTable
public import CFSG.Quasithin.Recognition.CertTitsJCheckInputs
public import Certificates.Certificate8073

public section

namespace CFSG.Quasithin

open CFSG.Certificates.Native CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.Tits

theorem jModel_check :
    jPel.size = 512 ∧ titsJBase = [5, 1, 24, 12] ∧ jGenArrs.size = 3 ∧
    (allLt 512 fun i => allLt 512 fun j => decide ((jMulT[i]!)[j]! < 512) &&
      titsJBase.all fun p => (jPel[(jMulT[i]!)[j]!]!)[p]! == (jPel[i]!)[(jPel[j]!)[p]!]!) = true ∧
    (allLt 512 fun i => decide (jInvT[i]! < 512) &&
      isInvA 1755 jPel[i]! (invCand 1755 jPel[i]!) &&
      eqA 1755 (invCand 1755 jPel[i]!) jPel[jInvT[i]!]!) = true ∧
    jOneI < 512 ∧ eqA 1755 jPel[jOneI]! (idA 1755) = true ∧
    jZI < 512 ∧ eqA 1755 jPel[jZI]! jZArr = true ∧
    (allLt 512 fun i => allLt 512 fun j => i == j || !(eqA 1755 jPel[i]! jPel[j]!)) = true ∧
    (allLt 3 fun k => isInvA 1755 jGenArrs[k]! jGenInvArrs[k]!) = true ∧
    (allLt 3 fun k => allLt 512 fun i => decide ((jCjT[k]!)[i]! < 512) &&
      eqA 1755 (compA 1755 (compA 1755 jGenArrs[k]! jPel[i]!) jGenInvArrs[k]!)
        jPel[(jCjT[k]!)[i]!]!) = true ∧
    isInvA 1755 jCArr jCInv = true ∧
    (allLt 512 fun i => decide (jCcT[i]! < 512) &&
      eqA 1755 (compA 1755 (compA 1755 jCArr jPel[i]!) jCInv) jPel[jCcT[i]!]!) = true ∧
    eqA 1755 (compA 1755 (compA 1755 (compA 1755 (compA 1755 jCArr jCArr) jCArr) jCArr) jCArr)
      (idA 1755) = true ∧
    VConds jOps jEB jFB jCc jCj jI0 jWtab :=
  Certificates.certificate8073

end CFSG.Quasithin
