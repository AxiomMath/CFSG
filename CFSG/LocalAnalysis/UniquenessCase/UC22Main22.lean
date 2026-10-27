module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Main21
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20u
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20h

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22.Ext

structure Global22h : Prop extends Global22g where
  diagram : uc22p20uDiagramInput

section Chain

variable {G : Type} [Group G] [Finite G]

theorem uc22m22_s20_4 (D : Data G) (hG : Global22e) (hr66 : UC6.R6_6 D) : S20_4 D :=
  s20_4_of D (s20_1_124 D hr66 hG.listB_nonabelian)
    (s20_2_of D hG.k318 (s20_1_124 D hr66 hG.listB_nonabelian))
    (s20_3_of D (s20_1_124 D hr66 hG.listB_nonabelian)
      (s20_2_of D hG.k318 (s20_1_124 D hr66 hG.listB_nonabelian)) hG.listB_nonabelian hG.schreier
      hG.dichotomy (uc22p20h_five D hG.threeNoncentral))
    hG.listB_nonabelian hG.listB_notSmall

theorem uc22m22_s20_10 {D : Data G} (hG : Global22h) (hr66 : UC6.R6_6 D) (h20_6 : S20_6 D) : S20_10 D :=
  uc22p20u_s20_10_of hG.diagram D (uc22m22_s20_4 D hG.toGlobal22g.toGlobal22e hr66)
    (uc22p20t_s20_7ref_of
      (uc22p20r_global22f_of_tables hG.griess hG.nativeGriess hG.excl hG.two) hG.listB_nonabelian
      hG.dichotomy D (s20_1_124 D hr66 hG.listB_nonabelian) h20_6)

end Chain

end CFSG.LocalAnalysis.UniquenessCase.UC22
