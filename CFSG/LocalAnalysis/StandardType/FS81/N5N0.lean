module

public import CFSG.LocalAnalysis.StandardType.FS81.EvenN0Line
public import CFSG.LocalAnalysis.StandardType.FS81.N5N0Line

public section

namespace CFSG.StandardType.FrameRoute.FS81

open scoped Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

theorem false_of_evenN0_five {Xg : Subgroup (GL (Fin 6) (ZMod 3))}
    (h : EvenN0MatHyp 5 Xg) : False := by
  obtain ⟨T, hTX, hT⟩ := h.exists_T
  exact false_of_conj_tau0_five hT hTX h.sub
    (fun A hA hfix => EvenN0MatHyp.comm_of_mem_H hT
      (h.mem_H_of_mulVec_e0 hA (c := 1) (by rw [hfix, one_smul])))
    (fun A hA hcomm =>
      EvenN0MatHyp.eq_zero_or_eq_smul_of_commute_tau0 hT hcomm)
    (fun A hA A' hA' c hc => h.conj_eq_of_mulVec_e0 hT hA hA' hc)
    (EvenN0Line.evenN0MatHyp_hroot (n := 5) (by decide) h)
    (fun A hA h0 => h.wt_two_of_O6 ⟨A, hA, rfl⟩ h0)

end CFSG.StandardType.FrameRoute.FS81

end
