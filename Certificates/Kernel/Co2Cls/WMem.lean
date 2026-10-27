module

public import Certificates.Kernel.Co2Cls.Classes
public import Certificates.Kernel.Co2Cls.WChecks

public section

namespace CertificateChecks.KernelSpor.Co2Cls

open CFSG.KC.Loop CFSG.KC.F2W CFSG.KC.Co2InvS CFSG.KC.Co2Syl CFSG.KC.TabMatGrp CFSG.KC.Co2Cls
  CertificateChecks.KernelSpor.Co2Syl

theorem wmem_of {W : List ℕ} {ws : List (List ℕ)} {n : ℕ} (hl : ∀ w ∈ ws, ∀ l ∈ w, l < 42)
    (hb : ∀ j < n, Nat.beq (lAt W j) (wordK (ws.getD j [])) = true) :
    ∀ j < n, MatP 22 (lAt W j) ∈ genMonN 21 GC := by
  intro j hj
  rw [Nat.eq_of_beq_eq_true (hb j hj)]
  refine wordK_mem _ fun l h => ?_
  rw [List.getD_eq_getElem?_getD] at h
  cases e : ws[j]? with
  | none => simp [e] at h
  | some w =>
    rw [e, Option.getD_some] at h
    exact hl w (List.mem_of_getElem? e) l h

theorem wmem1 : ∀ j < 2, MatP 22 (lAt W1 j) ∈ genMonN 21 GC :=
  wmem_of (words_lt _ (by simp)) word1
theorem wmem2 : ∀ j < 2, MatP 22 (lAt W2 j) ∈ genMonN 21 GC :=
  wmem_of (words_lt _ (by simp)) word2
theorem wmem3 : ∀ j < 2, MatP 22 (lAt W3 j) ∈ genMonN 21 GC :=
  wmem_of (words_lt _ (by simp)) word3
theorem wmem5 : MatP 22 (lAt W5 0) ∈ genMonN 21 GC :=
  wmem_of (words_lt _ (by simp)) word5 0 (by norm_num)
theorem wmem6 : MatP 22 (lAt W6 0) ∈ genMonN 21 GC :=
  wmem_of (words_lt _ (by simp)) word6 0 (by norm_num)
theorem wmem7 : ∀ j < 3, MatP 22 (lAt W7 j) ∈ genMonN 21 GC :=
  wmem_of (words_lt _ (by simp)) word7
theorem wmem8 : ∀ j < 3, MatP 22 (lAt W8 j) ∈ genMonN 21 GC :=
  wmem_of (words_lt _ (by simp)) word8
theorem wmem9 : MatP 22 (lAt W9 0) ∈ genMonN 21 GC :=
  wmem_of (words_lt _ (by simp)) word9 0 (by norm_num)

end CertificateChecks.KernelSpor.Co2Cls

end
