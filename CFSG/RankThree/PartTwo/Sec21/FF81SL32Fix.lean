module

public import CFSG.RankThree.PartTwo.Sec21.FF81SL32FixCore
public import CFSG.RankThree.PartTwo.Sec21.FF81Sec36Defs

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79 (Cen Nor)
open CFSG.RankThree.PartTwo.Sec21.FF81.SL32Fix (sl32Fix_core)

theorem kf_sl32Fix : KF_SL32Fix := by
  intro X _ _ K U W hK hU2 hWU hWn hKU hKW y hy hy3
  obtain ⟨φ⟩ := hK
  refine sl32Fix_core K U W φ hU2 hWU hWn (fun x hx u hu => ?_) (fun x hx w hw => ?_) hy hy3
  · exact (Subgroup.mem_normalizer_iff.1 (hKU hx) u).1 hu
  · exact (Subgroup.mem_normalizer_iff.1 (hKW hx) w).1 hw

end CFSG.RankThree.PartTwo.Sec21.FF81
