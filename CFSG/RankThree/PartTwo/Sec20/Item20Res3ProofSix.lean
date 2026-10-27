module

public import CFSG.RankThree.PartTwo.Sec20.OneTools

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem le_normalizer_omegaZOf_pCoreOf {K T : Subgroup G} :
    K ≤ Subgroup.normalizer (Sec3.omegaZOf (CFSG.Open.pCoreOf 2 (K ⊔ T)) : Set G) := by
  have : (CFSG.omegaOneCenter (⊤ : Subgroup ↥(CFSG.Open.pCoreOf 2 (K ⊔ T)))).Characteristic :=
    omegaOneCenter_top_characteristic
  exact le_sup_left.trans ((CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _).trans
    (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _))

end CFSG.RankThree.PartTwo.Sec20
