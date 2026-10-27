module

public import CFSG.RankThree.PartOne.S11c.Sec66ClassCommon
public import CFSG.RankThree.PartOne.S11d.OutClassicalTwo
public import CFSG.RankThree.PartOne.S11d.OutSymplectic

public section

namespace CFSG.RankThree.PartOne.Sec66T

open CFSG CFSG.Blueprint
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible StatedClassicalModel)

theorem sec66T_K2_PSp : Sec66T_K2 .PSp := by
  intro T _ _ p hp hp5 hmodel _ E hE hcard hEinn _hra
  obtain ⟨n, f, hadm, hM⟩ := hmodel
  have hC : StatedClassicalModel T .PSp n 2 f :=
    (lieModel_classical_iff (by decide)).mp hM
  have hn : 2 ≤ n := hadm.2.2.1
  by_cases hn3 : 3 ≤ n
  · exact no_plane_of_outPNice hp (OutStructure.outPNice_PSp_ge_three hp hn3 hC) E hE hcard hEinn
  · have hn2 : n = 2 := by omega
    subst hn2
    exact no_plane_of_outPNice hp (OutStructure.outPNice_PSp_two hp hC) E hE hcard hEinn

end CFSG.RankThree.PartOne.Sec66T
