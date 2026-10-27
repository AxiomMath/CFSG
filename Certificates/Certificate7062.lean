
module

public import Certificates.Certificate7062Base
import all Certificates.Certificate7062Base

import Certificates.Kernel.HMathieu.T22Glue
import Certificates.Kernel.HMathieu.T23Glue
import Certificates.Kernel.HMathieu.T24Glue

open CFSG CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.Mathieu CFSG.KC.HMathieu
open CertificateChecks.KernelHMathieu

namespace Certificates

open CertificateChecks.Batch7062 in
open CFSG CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.Mathieu CFSG.Monster.Code in
public theorem certificate7062 :
    (∀ s : T22s2.Elem, s ≠ 1 → s * s = 1 →
       (fixMasks 10 (fun q m => actM (matsC22[q.idx]!) m) [s]).length ≤ 2 ^ 7)
    ∧ (∀ s : T23s2.Elem, s ≠ 1 → s * s = 1 →
       (fixMasks 11 (fun q m => actM (matsC23[q.idx]!) m) [s]).length = 2 ^ 7)
    ∧ (∀ s : T24s2.Elem, s ≠ 1 → s * s = 1 →
       (fixMasks 11 (fun q m => actM (matsC24[q.idx]!) m) [s]).length ≤ 2 ^ 7)
    ∧ (inAutOK inv23Arr = true ∧ (∀ i < 24, inv23Arr[inv23Arr[i]!]! = i) ∧
       inv23Arr[0]! = 0 ∧ inv23Arr[1]! ≠ 1 ∧
       ((List.range (2 ^ 11)).filter fun m => act11 inv23Arr m == m).length = 2 ^ 7 ∧
       ((List.range (2 ^ 11)).filter fun m => actC11 inv23Arr m == m).length = 2 ^ 7 ∧
       ((List.range (2 ^ 11)).filter fun m => actC11 inv24Arr m == m).length = 2 ^ 7) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s h1 h2
    have hs : s ∈ inv22s2 := T22s2.mem_invols h1 h2
    rw [fixMasks_single]
    change ((List.range _).filter fun m => codeAct22 s m == m).length ≤ _
    rw [T22.codeAct_mem hs]
    refine allImg_sound Fix7062.c22 _ (getD_mem_take ?_ ?_)
    · rw [← T22.len]
      exact List.idxOf_lt_length_of_mem hs
    · rw [T22.mdOK, List.length_map, T22.lenP]
      have := List.idxOf_lt_length_of_mem hs
      rw [T22.len] at this
      omega
  · intro s h1 h2
    have hs : s ∈ inv23s2 := T23s2.mem_invols h1 h2
    have e : ∀ m, actM (matsC23[s.idx]!) m = actM (T23.Md.getD (inv23s2.idxOf s) []) m :=
      congrFun (T23.actC_mem hs)
    rw [fixMasks_single]
    simp only [e]
    have hk := List.idxOf_lt_length_of_mem hs
    rw [T23.len] at hk
    have hM := getD_mem_take (l := T23.Md) (r := 35) hk
      (by rw [T23.mdOK, List.length_map, T23.lenP]; omega)
    exact le_antisymm (allImg_sound Fix7062.c23.1 _ hM) (allKer_sound Fix7062.c23.2 _ hM)
  · intro s h1 h2
    have hs : s ∈ inv24s2 := T24s2.mem_invols h1 h2
    rw [fixMasks_single]
    change ((List.range _).filter fun m => codeAct24 s m == m).length ≤ _
    rw [T24.codeAct_mem hs]
    have hk := List.idxOf_lt_length_of_mem hs
    rw [T24.len] at hk
    exact allImg_sound Fix7062.c24 _
      (getD_mem_take hk (by rw [T24.mdOK, List.length_map, T24.lenP]; omega))
  · obtain ⟨p1, p2, p3, p4⟩ := Fix7062.plain4
    refine ⟨p1, p2, p3, p4, ?_, ?_, ?_⟩
    · exact count_eq (xorLin_act11 _) Fix7062.c4.1 Fix7062.c4.2 (by simp [Fix7062.mats4])
    · exact count_eq (xorLin_actC11 _) Fix7062.c4.1 Fix7062.c4.2 (by simp [Fix7062.mats4])
    · exact count_eq (xorLin_actC11 _) Fix7062.c4.1 Fix7062.c4.2 (by simp [Fix7062.mats4])

end Certificates
