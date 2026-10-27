module

public import CFSG.Sporadic.J4.QT2LocFiveNative
public import CFSG.Sporadic.J4.QT2LocCntNative
import Certificates.Kernel.J4Q.LocM
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.Batch40344

open CFSG.Sporadic.J4 CFSG.KD.J4Q

theorem fiveAct_407 : QT2.fiveAct 407 = 407 := Nat.eq_of_beq_eq_true (by quickRfl)

theorem mem_zMasks_407 : (407 : Nat) ∈ QT2.zMasks := by
  have h : ZML.contains 407 = true := by quickRfl
  rw [KernelJ4Q.zMasks_ZML]
  exact List.elem_iff.1 h

end CertificateChecks.Batch40344

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.J4 in
theorem certificate40344 : QT2.fiveAct 407 = 407 ∧ (407 : Nat) ∈ QT2.zMasks :=
  ⟨CertificateChecks.Batch40344.fiveAct_407, CertificateChecks.Batch40344.mem_zMasks_407⟩

end Certificates
