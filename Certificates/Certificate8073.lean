
module

public import CFSG.Quasithin.Recognition.CertTitsJCheckInputs
import Certificates.Kernel.Misc.Tits.JVConds8073

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Quasithin CFSG.Certificates.Native CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.Schreier.Tits in
theorem certificate8073 :
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
    VConds jOps jEB jFB jCc jCj jI0 jWtab := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩ :=
    KernelMisc.TitsJT.table_facts
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15,
    KernelMisc.TitsJT.V.vconds⟩

end Certificates
