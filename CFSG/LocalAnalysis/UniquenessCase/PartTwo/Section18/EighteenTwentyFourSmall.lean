module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.Assembly
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.WeakClosureOrbit
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen67SmallVtil

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

namespace S17

theorem gap17_5_A6Pair_of_mSub_le_two {D : Data G} {V₀ V : Subgroup G}
    (h : mSub V₀ ≤ 2) : Gap17_5_A6Pair D V₀ V :=
  fun hV _ _ _ _ _ _ _ _ =>
    Small.card_le_four_of_mSub_le_two hV.pairFacts.elemAbelian₀.isPGroup h

end S17

namespace S18

theorem eighteen_twentyfour_of1669_small (D : Data G)
    (h65 : ∀ V₀ V, Hyp125 D V₀ V → MBarGT D.M V₀ V 3 → mSub V₀ ≤ 1 → S17.R17_65At D V₀ V)
    (h1742 : ∀ V₀ V, Hyp125 D V₀ V → MBarGT D.M V₀ V 3 → mSub V₀ ≤ 1 → S17.R17_42At D V₀ V)
    (h14 : ∀ V₀ V p L (h : Hyp18 D V₀ V p L), MBarGT D.M V₀ V 3 → R18_14_2At D V₀ V p L h)
    (h16 : ∀ V₀ V p L (h : Hyp18 D V₀ V p L), MBarGT D.M V₀ V 3 → R18_16_2At D V₀ V p L h)
    (h17 : ∀ V₀ V p L (h : Hyp18 D V₀ V p L), MBarGT D.M V₀ V 3 → R18_17_2At D V₀ V p L h)
    (h22 : ∀ V₀ V p L (h : Hyp18 D V₀ V p L), MBarGT D.M V₀ V 3 → R18_22At D V₀ V p L h)
    (h23 : ∀ V₀ V p L (_h : Hyp18 D V₀ V p L), MBarGT D.M V₀ V 3 → R18_23At D V₀ V p L)
    (hx : DataExt D) (h61 : UC6.R6_1 D) (h126 : R126 D) (h66 : UC6.R6_6 D) (h127 : R127 D)
    (h1114 : R1114 D) (h111 : W3Thm111 G) (h183 : W3Thm183 G) (hSg : UC6S846.SigmaStd D) :
    R18_24Of1669 D := by
  intro V₀ V hV hm
  by_contra hle
  have hs : mSub V₀ ≤ 1 := Nat.le_of_not_lt hle
  exact hle (eighteen_twentyfour_of1669_loc D (fun _ _ _ _ => h65 V₀ V hV hm hs)
    (fun _ _ _ _ => h1742 V₀ V hV hm hs) h14 h16 h17 h22 h23 hx h61 h126 h66 h127 h1114 h111
    h183 hSg V₀ V hV hm)

end S18

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
