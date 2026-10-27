module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveSevenB
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5ASTwelve
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.NineThreeSylData

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem r127_of_twelve_seven_AS_syl
    (hTim : CFSG.CGT.Timmesfeld75.NodeStatement) (hcat : ¬ CFSG.Blueprint.Catalog G)
    (D : Data G) (h5_11 : WeakClosure81.Asch5_11AS) (h5_13 : WeakClosure81.Asch5_13AS)
    (h63 : UC6.R6_3 D) (h66 : UC6.R6_6 D) (h86 : W3Lem86_1 G) (h88 : W3Thm88 G)
    (h93 : ∀ V : Subgroup G, WeakClosure81.Thm93Syl V D.T) : R127 D :=
  fun h124 V hV hTI h8 =>
    have h := twelve_seven hTim hcat D h63 h66 h86 h88
      (WeakClosure81.r126_of_twelve_six_AS D h5_11 h5_13 h66) h124 hV hTI h8
      (thm93_of_thm93Syl D hV (h93 V))
    ⟨h.2.1, fun hz => (h.2.2 hz).2⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
