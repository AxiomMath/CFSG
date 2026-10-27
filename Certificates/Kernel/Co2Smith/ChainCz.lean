module

public import Certificates.Kernel.Co2Smith.Cent
public import Certificates.Kernel.Co2Smith.ChainCzJ
public import Certificates.Kernel.Co2Smith.ChainCzK
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo2Smith

open CFSG.KC.Co1F2 CFSG.KC.Co2Smith CFSG.KC.Enum CFSG.KS CFSG.KS.Raw
open CFSG.Sporadic.Co2Smith.Native

theorem chainCz_ok :
    glChainCzOK = true := by
  have hB := chCzBind_k
  have hO := chCzO_k
  have hM := czMaps_k
  have hC := czCent_k
  have hl : glCzWords.length = 21 := by decide
  have hget : ∀ i < glCzWords.length, glCzWords[i]! = glCzWords.getD i [] := fun i hi => by
    rw [getElem!_pos glCzWords i hi, List.getD_eq_getElem _ _ hi]
  have hc : glChainOK glCzWords glChainCzBase glChainCzW 743178240 = true := by
    refine chainOK_of_card (D := chCzD) (G := CzGP) (K := centX) (fun i hi => ?_) (fun i hi => ?_)
      (fun i hi => ?_) rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) CCz.head
      CCz.ho (by norm_num) (fun i hi => ?_) (card_cent_le (le_refl _)) (by decide +kernel)
    · have h := allN_spec hB i (by omega)
      simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
      rw [hget i hi]
      exact h.1
    · have h := allN_spec hB i (by omega)
      simp only [Bool.and_eq_true] at h
      rw [hget i hi]
      exact h.2
    · exact Nat.eq_of_beq_eq_true (allN_spec hO i (by omega))
    · have h := allN_spec hC i (by omega)
      simp only [Bool.and_eq_true] at h
      exact mem_centX h.1.1 h.1.2 h.2
  unfold glChainCzOK
  rw [hc, Bool.and_true]
  simp only [List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hM ⊢
  intro k hk
  rw [glR_eq (fun j hj => by rw [List.mem_singleton.1 hj]; exact (hM k hk).1),
    glMaps_unpack _ (by decide) (by decide)]
  exact (hM k hk).2

end CertificateChecks.KernelCo2Smith
