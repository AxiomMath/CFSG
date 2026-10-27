module

public import CFSG.RankThree.PartTwo.Sec20.TwoItems45
import CFSG.RankThree.PartTwo.Sec19.Item1923
import CFSG.RankThree.PartTwo.Sec19.Hyp1921NotLeM

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late


theorem not_hyp1921_of_items
    (h1912 : Item1912) (hkf : KFacts1923)
    (h202 : ∀ (G : Type) [Group G] [Finite G] (A M L N : Subgroup G) (c : G),
      Hyp201 G A M L N c → Hyp1921 G A M N L →
        scriptM ((A ⊔ kTwenty M c : Subgroup G) : Set G) = {M})
    (h208 : Item208Two) (h209 : Item209Two) :
    ∀ (G : Type) [Group G] [Finite G] (A M N L : Subgroup G), ¬ Hyp1921 G A M N L := by
  have h23 : Item1923 := item1923_of_kfacts h1912 hkf
    (item1922Facts_of_item1922Full (item1922Full_of_item1912 h1912))
  have h204 := item204Two_of h1912 hkf.h194 h23 h202
  have h205 := item205Two_of h1912 hkf.h194 h23 h204
  exact fun G _ _ A M N L => not_hyp1921_of_two h204 h205 h208 h209 (item1922_of_item1912 h1912)

end CFSG.RankThree.PartTwo.Sec20
