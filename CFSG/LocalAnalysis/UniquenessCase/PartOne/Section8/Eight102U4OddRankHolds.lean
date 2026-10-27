module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102KFacts
import CFSG.Adapters.LieModelTorusRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

theorem kU4OddRank_holds : KU4OddRank := by
  intro X _ _ n h hn
  have h3 : 3 ∣ 2 ^ n + 1 := by
    simpa using Odd.nat_add_dvd_pow_add_pow 2 1 hn
  exact CFSG.Blueprint.LieModel.le_pRank_psu_of_dvd h Nat.prime_three h3 (by norm_num)
    (Or.inr (by norm_num))

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

end
