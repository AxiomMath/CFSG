module

public import CFSG.ClassicalInvolution.SmallCases.NobqJ2Inputs
import Certificates.Kernel.SchreierFam.J2Cq
import CFSG.Certificates.Kernel.SchreierFam.All3Sound
import CFSG.Certificates.Kernel.SchreierFam.CqKSound

namespace CertificateChecks.Batch9302

open CFSG CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Nobq CFSG.ComponentClassification.J2Cover
  CFSG.Sporadic.RuSchreier CFSG.ClassicalInvolution.J2Data CFSG.ClassicalInvolution.J2Proof
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KC.Misc.ArrEnum
  CFSG.KS.SchreierFam CFSG.KC.BfsPin CertificateChecks.KernelJ2Cover CertificateChecks.KernelSchreierFam

theorem hsz : szOK 315 9 = true := by decide +kernel

theorem gens_bind : ∀ k < [cent2AStrong[0]!, cent2AStrong[1]!].length,
    [cent2AStrong[0]!, cent2AStrong[1]!][k]! = unpack 315 9 (C2A.S k) ∧ PP 315 9 (C2A.S k) := by
  intro k hk
  have hk2 : k < 2 := by simpa using hk
  refine ⟨?_, PP_of_permOK' hsz (allN_spec c2A_perm k (by omega))⟩
  rw [← c2A_binds.2.2.2.2.1 k (by omega)]
  interval_cases k <;> rfl

theorem words_ok : ∀ l ∈ J2Cq.cqWords, l.length ≤ 4 ∧
    ∀ i ∈ l, i < [cent2AStrong[0]!, cent2AStrong[1]!].length := by
  decide

theorem cqAll : all3 315 cent2ALevels (cqTestA 315 twoAArr cent2AWit) = true := by
  rw [arrBind_sound J2Cq.tBind]
  exact all3_of_K c2A_binds c2A_perm C2A.hl (by norm_num)
    (fun G hG hQ => cqK_sound hsz J2Cq.tCanon gens_bind words_ok hG hQ) J2Cq.cqAll

end CertificateChecks.Batch9302

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Nobq in
open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.ComponentClassification.J2Cover CFSG.Sporadic.RuSchreier CFSG.ClassicalInvolution.J2Data
  CFSG.ClassicalInvolution.J2Proof in
theorem certificate9302 : all3 315 cent2ALevels (cqTestA 315 twoAArr cent2AWit) = true :=
  CertificateChecks.Batch9302.cqAll

end Certificates
