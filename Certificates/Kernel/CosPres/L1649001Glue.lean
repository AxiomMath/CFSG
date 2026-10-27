module

public import CFSG.LocalAnalysis.StandardType.GGQTwoSixPointInputs
import Certificates.Kernel.CosPres.L1649001
import CFSG.Certificates.Kernel.ActLBSound

public section

namespace CFSG.KD.L1649001

open CFSG.KC CFSG.KC.YModel CFSG.KC.ActLB CFSG.CosetTable CFSG.StandardType.QTwo.SixPoint

theorem index_chart5_ge_of_finiteIndex
    (hfi : (genSub {r : FreeGroup (Fin 18) | r ∈ relsP.map FreeGroup.mk}
      (subsetOf 18 chart5)).FiniteIndex) :
    8064 ≤ (genSub {r : FreeGroup (Fin 18) | r ∈ relsP.map FreeGroup.mk}
      (subsetOf 18 chart5)).index := by
  refine CFSG.KS.ActLB.le_index_of_checks (k := 13) (Nf := Nf) (R := 7) (by norm_num) ?_
    ch1649001inv ch1649001rels ?_ ch1649001orb hfi
  · intro c hc
    have h : ch1649001net c = true := by
      interval_cases c
      exacts [ch1649001net0, ch1649001net1, ch1649001net2, ch1649001net3, ch1649001net4,
        ch1649001net5, ch1649001net6, ch1649001net7, ch1649001net8, ch1649001net9,
        ch1649001net10, ch1649001net11, ch1649001net12, ch1649001net13, ch1649001net14,
        ch1649001net15, ch1649001net16, ch1649001net17, ch1649001net18, ch1649001net19,
        ch1649001net20, ch1649001net21, ch1649001net22, ch1649001net23, ch1649001net24,
        ch1649001net25, ch1649001net26, ch1649001net27, ch1649001net28, ch1649001net29,
        ch1649001net30, ch1649001net31, ch1649001net32, ch1649001net33, ch1649001net34,
        ch1649001net35]
    exact h
  · intro x hx
    have hc : x.val ∈ chart5 := by
      have := (List.mem_filter.mp hx).2
      simpa using this
    obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hc
    have hi' : i < 14 := hi
    have h : ch1649001fix i = true := by
      interval_cases i
      exacts [ch1649001fix0, ch1649001fix1, ch1649001fix2, ch1649001fix3, ch1649001fix4,
        ch1649001fix5, ch1649001fix6, ch1649001fix7, ch1649001fix8, ch1649001fix9,
        ch1649001fix10, ch1649001fix11, ch1649001fix12, ch1649001fix13]
    unfold ch1649001fix at h
    rw [List.getD_eq_getElem _ _ hi, he] at h
    exact h

end CFSG.KD.L1649001

end
