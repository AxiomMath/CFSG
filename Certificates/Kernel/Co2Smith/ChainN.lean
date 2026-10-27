module

public import Certificates.Kernel.Co2Smith.Chain
public import Certificates.Kernel.Co2Smith.ChainNJ
public import Certificates.Kernel.Co2Smith.ChainNK
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo2Smith

open CFSG.KC.Co1F2 CFSG.KC.Co2Smith CFSG.KC.Enum CFSG.KS CFSG.KS.Raw
open CFSG.Sporadic.Co2Smith.Native

theorem chainN_ok : glChainNOK = true := by
  have hB := chNBind_k
  have hO := chNO_k
  have hl : glNWords.length = 11 := by decide
  have hget : ∀ i < glNWords.length, glNWords[i]! = glNWords.getD i [] := fun i hi => by
    rw [getElem!_pos glNWords i hi, List.getD_eq_getElem _ _ hi]
  unfold glChainNOK
  refine chainOK_of (D := chND) (G := NGP) (fun i hi => ?_) (fun i hi => ?_) (fun i hi => ?_) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel) CN.head CN.hl (by norm_num) CN.hs
    (by decide +kernel)
  · have h := allN_spec hB i (by omega)
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
    rw [hget i hi]
    exact h.1
  · have h := allN_spec hB i (by omega)
    simp only [Bool.and_eq_true] at h
    rw [hget i hi]
    exact h.2
  · exact Nat.eq_of_beq_eq_true (allN_spec hO i (by omega))

end CertificateChecks.KernelCo2Smith
