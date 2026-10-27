module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenTwentySixA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.GapNEHolds
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5ASTwelve
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open CFSG.Open Subgroup CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.LocalAnalysis.WeakClosure81

variable {G : Type} [Group G] [Finite G]

theorem normalizer_w_two_not_le (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L K : Subgroup G)
    (h : Ctx19_1 D V₀ V p L K)
    (h5_11 : Asch5_11AS) (h5_13 : Asch5_13AS) (h66 : UC6.R6_6 D)
    (h861 : W3Lem86_1 G) (hTim : CFSG.CGT.Timmesfeld75.NodeStatement)
    (hcat : ¬ CFSG.Blueprint.Catalog G) (hm : 4 < mSub V₀) :
    ¬ Subgroup.normalizer (E3.wClos V₀ 2 D.T : Set G) ≤ D.M := by
  obtain ⟨H₀, hmin⟩ := h.hyp.hyp125.exists_hyp124Min
  exact S17.normalizer_Wi_two_not_le D V₀ V H₀ h.hyp.hyp125 hmin
    (r126_of_twelve_six_AS D h5_11 h5_13 h66) h861 hm hTim hcat
    (S17.gap17_26_NE_holds D V₀ V H₀ h5_11 h5_13 h66 h861 hTim hcat)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
