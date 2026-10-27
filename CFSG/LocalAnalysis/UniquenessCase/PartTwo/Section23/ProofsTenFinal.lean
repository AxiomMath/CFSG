module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsTen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ComponentShapes
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProductComponents

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s23_10_of (hJ : J1NotSp4SU3) (D : Data G) (Ch : Choice2011 G)
    (h54 : S23_5_4 D Ch) (h6 : S23_6 D Ch) (h8 : S23_8 D Ch) (h2121 : S21_21B D Ch)
    (h2123 : S21_23 D Ch) (hsig : D.sig.Nonempty) : S23_10 D Ch :=
  s23_10_of_parts D Ch h54 h6 h2121 h2123 hsig
    (fun h1930 c => hyp2120_two_of_s23_8 hJ D Ch h8 h1930 c)
    (by
      intro h1930 c n hn A B _ _ e hA hB
      exact false_of_s23_8_of_hinf_prod D Ch h8 h1930 c hn e hA hB)

end CFSG.LocalAnalysis.UniquenessCase.UC22
