module

public import CFSG.Quasithin.AppendixH.H15.H157Inputs
import Certificates.Kernel.HMathieu.Odd490013
import CFSG.Certificates.Kernel.HMathieu.OddSound
import CFSG.Certificates.Kernel.HMathieu.PickJSound

open CFSG.KC.Enum CFSG.KS CFSG.KC.HMathieu CFSG.Quasithin.H.Mathieu CFSG.ASVolI.AppH.H157
  CertificateChecks.KernelHMathieu.Odd

namespace CertificateChecks.Batch490013

open CFSG.KC.Enum CFSG.KS CFSG.KC.HMathieu CFSG.Quasithin.H.Mathieu CFSG.ASVolI.AppH.H157
  CertificateChecks.KernelHMathieu.Odd

theorem ok_of {T : PT 24} [Fact (T.check = true)] {cc lift : List Nat} {n r fuel : Nat} {gens E : List Nat}
    {Js : List (List Nat)} (hT : T = PT.ofGens 24 (gens.map unpk) fuel)
    (h : oddOK cc lift n r fuel gens E Js = true) {ok : Array Nat → Bool}
    (ht : tail490013 ok E = true) (s : T.Elem) (hs : s ≠ 1) : ok (T.arr s) = true := by
  have H := packed_of_oddOK hT h
  have hidx : s.idx ≠ 0 := fun e => hs (PT.Elem.ext' (by rw [e, PT.idx_one, H.one]))
  obtain ⟨hlt, harr⟩ := arr_of_oddOK hT h s
  rw [harr]
  unfold tail490013 at ht
  rw [List.all_eq_true] at ht
  refine ht _ ?_
  have e : E.getD s.idx 0 = (E.drop 1)[s.idx - 1]'(by simp; omega) := by
    rw [List.getElem_drop, List.getD_eq_getElem _ _ hlt]
    congr 1
    omega
  rw [e]
  exact List.getElem_mem _

theorem fix_le {T : PT 24} [Fact (T.check = true)] (s : T.Elem)
    (h : okR490013 (T.arr s) = true) : fixCnt (matsOf11 T) s ≤ 8 := by
  have hl := rankOK_matOf (xorLin_act11 (T.arr s)) h
  have e : fixCnt (matsOf11 T) s =
      ((List.range (2 ^ 11)).filter fun m => act11 (T.arr s) m == m).length := by
    unfold fixCnt fixMasks
    refine congrArg List.length (List.filter_congr fun m hm => ?_)
    simp only [List.all_cons, List.all_nil, Bool.and_true]
    rw [actM_mats11 T rfl s (List.mem_range.1 hm)]
  rw [e]
  exact hl

end CertificateChecks.Batch490013

namespace Certificates

open CertificateChecks.Batch490013

open CFSG.ASVolI.AppH.H157 in
public theorem certificate490013 : class3AHolds := by
  have h5 : oddOK κCCols liftCCols 11 6 32 (G.getD 5 []) (E.getD 5 []) (J.getD 5 []) = true := oddK5
  have h6 : oddOK κCCols liftCCols 11 7 16 (G.getD 6 []) (E.getD 6 []) (J.getD 6 []) = true := oddK6
  have h7 : oddOK κCCols liftCCols 11 7 16 (G.getD 7 []) (E.getD 7 []) (J.getD 7 []) = true := oddK7
  have h8 : oddOK κCCols liftCCols 11 7 16 (G.getD 8 []) (E.getD 8 []) (J.getD 8 []) = true := oddK8
  have h9 : oddOK κCCols liftCCols 11 7 32 (G.getD 9 []) (E.getD 9 []) (J.getD 9 []) = true := oddK9
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro p hp h16
    have hok := ok_of (by unfold T24s3; congr 1) h5 c490013s3 p hp
    unfold okA490013 at hok
    rcases Bool.or_eq_true_iff.1 hok with hc | hr
    · obtain ⟨h, hh, hb⟩ := List.any_eq_true.1 hc
      simp only [Bool.and_eq_true] at hb
      exact ⟨h, hh, hb.2, hb.1⟩
    · have hl := fix_le p hr
      unfold mats24s3 at h16
      omega
  · intro p hp
    have hl := fix_le p (ok_of (by unfold T24s5; congr 1) h6 c490013s5 p hp)
    unfold mats24s5
    omega
  · intro p hp
    have hl := fix_le p (ok_of (by unfold T24s7; congr 1) h7 c490013s7 p hp)
    unfold mats24s7
    omega
  · intro p hp
    have hl := fix_le p (ok_of (by unfold T24s11; congr 1) h8 c490013s11 p hp)
    unfold mats24s11
    omega
  · intro p hp
    have hl := fix_le p (ok_of (by unfold T24s23; congr 1) h9 c490013s23 p hp)
    unfold mats24s23
    omega

end Certificates
