module

public import Certificates.Kernel.Co2Smith.Chain
public import Certificates.Kernel.Co2Smith.ChainM2J
public import Certificates.Kernel.Co2Smith.ChainM2K
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo2Smith

open CFSG.KC.Co1F2 CFSG.KC.Co2Smith CFSG.KC.Enum CFSG.KS CFSG.KS.Raw
open CFSG.Sporadic.Co2Smith.Native

theorem chainM2_ok : glChainM2OK = true := by
  have hB := chM2Bind_k
  have hO := chM2O_k
  have hl : glM2Words.length = 3 := by decide
  have hget : ∀ i < glM2Words.length, glM2Words[i]! = glM2Words.getD i [] := fun i hi => by
    rw [getElem!_pos glM2Words i hi, List.getD_eq_getElem _ _ hi]
  unfold glChainM2OK
  refine chainOK_of (D := chM2D) (G := M2GP) (fun i hi => ?_) (fun i hi => ?_) (fun i hi => ?_) rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel) CM2.head CM2.hl (by norm_num)
    CM2.hs (by decide +kernel)
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
