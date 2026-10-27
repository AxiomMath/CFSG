module

public import Certificates.Kernel.Co2Smith.Chain
public import Certificates.Kernel.Co2Smith.Root
public import Certificates.Kernel.Co2Smith.ChainG0J
public import Certificates.Kernel.Co2Smith.ChainG0K
public import CFSG.Certificates.Kernel.Spor.RawSiftKConv
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo2Smith

open CFSG.KC.Co1F2 CFSG.KC.Co2Smith CFSG.KC.Enum CFSG.KS CFSG.KS.Raw
open CFSG.Sporadic.Co2Smith.Native CFSG.Certificates.Native

@[expose] def rtIdx (r t : Nat) : Nat := if r < 12 then 3 * r + (t - 1) else r + 24

theorem rtIdx_spec {r t : Nat} (hr : r < 18) (ht : t ∈ glParams r) :
    rtIdx r t < 42 ∧ rtR (rtIdx r t) = r ∧ rtT (rtIdx r t) = t := by
  unfold glParams at ht
  unfold rtIdx rtR rtT
  by_cases h : r < 12
  · rw [if_pos h] at ht ⊢
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl <;> refine ⟨by omega, ?_, ?_⟩ <;>
      simp only [show 3 * r + (1 - 1) < 36 by omega, show 3 * r + (2 - 1) < 36 by omega,
        show 3 * r + (3 - 1) < 36 by omega, if_true] <;> omega
  · rw [if_neg h] at ht ⊢
    simp only [List.mem_singleton] at ht
    subst ht
    refine ⟨by omega, ?_, ?_⟩ <;> simp only [show ¬ r + 24 < 36 by omega, if_false] <;> omega

theorem chainG0_ok : glChainG0OK = true := by
  have hB := chG0Bind_k
  have hO := chG0O_k
  have hRT := rtBind_k
  have hSf := rtSift_k
  have hget : ∀ i < glG0Words.length, glG0Words[i]! = glG0Words.getD i [] := fun i hi => by
    rw [getElem!_pos glG0Words i hi, List.getD_eq_getElem _ _ hi]
  have hl : glG0Words.length = 13 := by decide
  have hw : ∀ i < glG0Words.length, ∀ k ∈ glG0Words[i]!, k < 22 := by
    intro i hi
    have h := allN_spec hB i (by omega)
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
    rw [hget i hi]
    exact h.1.1
  have hG : ∀ i < glG0Words.length,
      bindVK (KernelSporSch.Co2M.PV 0) (G0GP i) (trK 22 (wK LP glG0Words[i]!)) = true := by
    intro i hi
    have h := allN_spec hB i (by omega)
    simp only [Bool.and_eq_true] at h
    rw [hget i hi]
    exact h.1.2
  have hOi : ∀ i < glG0Words.length,
      pcomp 2300 12 (mask 12) (pcomp 2300 12 (mask 12) CK (G0GP i)) CIK = CG0.S i :=
    fun i hi => Nat.eq_of_beq_eq_true (allN_spec hO i (by omega))
  obtain ⟨hb, -⟩ := chainBinds_of (D := chG0D) (W := glChainG0W) (base := glChainG0Base)
    (PSI := CG0.SI) (kS := 19) (nb := 5) (BP := CG0.BP) hw hG hOi rfl (by decide +kernel)
    (by decide +kernel) CG0.head
  have hp : allN 19 (fun j => permOK 2300 12 (mask 12) (2300 * 12) (CG0.S j) (CG0.SI j)) = true := by
    have h := CG0.head
    unfold headK at h
    simp only [Orb.bAnd_eq, Bool.and_eq_true] at h
    exact h.2.2.2.2.1
  have hrt : ∀ k < 43, bindVK (KernelSporSch.Co2M.PV 0) (RTP k) (trK 22 (rtM k)) = true ∧
      allN 2300 (fun i => Nat.blt (pg 12 (mask 12) (rtPsi k) i) 2300) = true := by
    intro k hk
    have h := allN_spec hRT k hk
    simp only [Bool.and_eq_true] at h
    exact h
  have hpsi : ∀ k < 43, glPsiArr (unpackR 22 (rtM k)) = unpack 2300 12 (rtPsi k) :=
    fun k hk => psi_eq (hrt k hk).1
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hSf
  obtain ⟨⟨hsift, hga⟩, hhi⟩ := hSf
  unfold glChainG0OK
  simp only [Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true']
  refine ⟨⟨⟨⟨?_, fun w hw' => ?_⟩, ?_⟩, ?_⟩, fun r hr t ht => ?_⟩
  · refine chainOK_of (D := chG0D) (G := G0GP) hw hG hOi rfl (by decide +kernel)
      (by decide +kernel) (by decide +kernel) CG0.head CG0.hl (by norm_num) CG0.hs
      (by decide +kernel)
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hw'
    have h := allN_spec hB i (by omega)
    simp only [Bool.and_eq_true] at h
    rw [← getElem!_pos glG0Words i hi, glR_eq (hw i hi),
      glMaps_unpack _ (by decide) (by decide), hget i hi]
    exact h.2
  · have e : rtM 42 = gaK := rfl
    rw [glGa_eq, ← e]
    exact permOK_of (hrt 42 (by decide)).1
  · have e : rtM 42 = gaK := rfl
    rw [glGa_eq, ← e, hpsi 42 (by decide)]
    exact Orb.siftA_false_of_K hb hp CG0.hl sz_ok (Nat.eq_of_beq_eq_true hhi)
      (hrt 42 (by decide)).2 hga
  · rw [List.mem_range] at hr
    obtain ⟨hk, hR, hT⟩ := rtIdx_spec hr ht
    have e : rtM (rtIdx r t) = rootK r t := by
      unfold rtM
      rw [if_pos hk, hR, hT]
    rw [glRootRows_eq, ← e]
    refine ⟨permOK_of (hrt _ (by omega)).1, ?_⟩
    rw [hpsi _ (by omega)]
    exact Orb.siftA_of_K hb hp CG0.hl rfl (hrt _ (by omega)).2 (allN_spec hsift _ hk)

end CertificateChecks.KernelCo2Smith
