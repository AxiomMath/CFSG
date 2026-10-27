
module

public import CFSG.Monster.B.TwoA.Unitary.Stab891Inputs
public import Certificates.Kernel.MonsterB.Co2Mem
import CFSG.Certificates.Kernel.Common.Harness

@[expose] public section

open CFSG.Monster.B.Co2 CFSG.Monster.B.TwoA.Unitary CertificateChecks.KernelMonB

namespace CertificateChecks.Batch3061

theorem kVec0 : Nat.beq (vecF 0) 6144 = true := by quickRfl

theorem shortVec_zero : Native.vectors[0]! = 6144 := by
  rw [vectors_getElem! (by decide)]
  exact Nat.eq_of_beq_eq_true kVec0

theorem spanIdxN_ok : ∀ i < 21, spanIdxN.getD i 0 < 891 ∧
    n6VecArr[spanIdxN.getD i 0]! = n6SpanArr[i]! := by
  decide +kernel

end CertificateChecks.Batch3061

namespace Certificates

end Certificates
