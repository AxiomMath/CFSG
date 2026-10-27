module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.PartTwo.Late.Defs
public import CFSG.RankThree.PartTwo.NotationBlocks

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem normalizer_eq_of_le {M V : Subgroup G} (hM : IsMaximalTwoLocal M) (hV1 : V ≠ ⊥)
    (hV2 : IsPGroup 2 V) (hMV : M ≤ Subgroup.normalizer (V : Set G)) :
    Subgroup.normalizer (V : Set G) = M := by
  by_contra hne
  exact hM.2 _ (lt_of_le_of_ne hMV (Ne.symm hne)) ⟨V, hV1, hV2, rfl⟩

end CFSG.RankThree.PartTwo.Sec20
