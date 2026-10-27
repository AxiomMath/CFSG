module

public import CFSG.RankThree.PartTwo.Sec13.Item134Arg128Fail
public import CFSG.RankThree.PartTwo.Sec13.Item134Holds

public section

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.ABGLocalTools (IsSylowOf)

theorem item134Arg128_of_item128BarAt
    (h128 : Sec12.Item128BarAt) (h45 : Sec4.Item4_5)
    (h131 : Item131) (hspor : SporadicModels131) (h415 : Sec4.Item4_15)
    (h414 : Sec4.Item4_14_local) (h422 : Sec4.Item4_22) (h48 : Sec4.Item4_8)
    (hJs : IsSimpleGroup CFSG.Blueprint.NativeSporadic.J2) : Item134Arg128 := by
  intro G _ _ A c L h hJ d hdA hd1 hS K hK hLK hKeq hA6 hW
  by_cases hP : ∃ P : Subgroup G, IsSylowOf 3 P
      (Subgroup.normalizer (A : Set G) ⊓ Subgroup.normalizer (Subgroup.zpowers d : Set G)) ∧
      ¬ Subgroup.zpowers c ⊔ Subgroup.zpowers d ≤ (Subgroup.center P).map P.subtype
  · exact item134Arg128_of_exists_sylow h128 h131 hspor h415 h45 h422 hJs h hJ hdA hd1 hS hK hLK
      hKeq hA6 hW hP
  · push Not at hP
    obtain ⟨-, heq, -, -⟩ := facts134 h131 hspor h415 h hJ hdA hd1 hS hK hLK hKeq hA6
    exact item134Arg128_of_central h45 h131 hspor h415 h414 h422 h48 G A c L h hJ d hdA hd1 hS K
      hK hLK hKeq hA6 hW fun P hP' => by rw [heq]; exact hP P hP'

end CFSG.RankThree.PartTwo.Sec13
