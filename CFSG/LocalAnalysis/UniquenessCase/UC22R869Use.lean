module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22ui
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21p

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem uc22p22u_r1110W_of_R117W (D : Data G) (hSig : UC6S846.SigmaStd D) (h61 : UC6.R6_1 D)
    (h63 : UC6.R6_3 D) (h77 : F07.R77Eq D) (h117 : R117W D) (h111 : F11.R111 D)
    (h112 : F11.R112 D) (hThin : CFSG.LocalAnalysis.UniquenessCase.PartTwo.ThinList13)
    (hCyc : CFSG.RankThree.PartTwo.Sec11.CyclicSylowThreeOutAbelian) : R1110W D := by
  have h116 := uc22p22u_c116W D hSig h61 h63 h77 h111 h112
  have h118 := uc22p22u_r118W hThin hCyc D h116 h117
  intro V hV hNorm p hp hp2 P hP
  refine ⟨uc22p22u_r1110_part1 D h118 hV hp hp2 hP, uc22p22u_r1110_part2 D h116 hV hp hp2 hP, ?_⟩
  intro n hn Xbar hXn hXe hXc hXle
  refine ⟨uc22p22u_r1110_part3a D h116 h118 hV hp hp2 hP hn hXe hXc hXle, ?_⟩
  intro hσ v hv _ hrank
  exact uc22p22u_r1110_part3b D hSig h61 h63 h77 h116 h118 hV hp hp2 hP hXe hXle hσ hv hrank

end CFSG.LocalAnalysis.UniquenessCase.UC22
