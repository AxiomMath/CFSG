module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPC2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
section
open CFSG.Open
open CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo.Sec4
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data IsSpor)
variable {G : Type} [Group G] [Finite G]
variable {D : Data G}
variable (c : Ctx82E3 D) {P A : Subgroup G} {a : G}

theorem zSub_card'
    (hON : UCK.ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    (h7 : D.sig = {7}) (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M) :
    Nat.card (zSub P c.L) = 3 :=
  card_zSub_of_onan' c hON hP

end
end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
