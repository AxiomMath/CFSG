module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3R920KFact
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3R920KFactWreath
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3R920KFactOddProps

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Blueprint (LieModel)

theorem kFactL28_L3U3_odd {Q : Type} [Group Q] [Finite Q] {p f : ℕ} (hp : p ≠ 2)
    (hQ : LieModel Q .PSL 3 p f ∨ LieModel Q .PSU 3 p f) {X W T : Subgroup Q}
    (c : KCfgL28 X W T) : False :=
  false_of_isL2_three_of_two_subgroups
    (fun R hR => exists_abelian_index_two_of_isPGroup_two_L3U3 hp hQ R hR)
    (pRank_two_le_two_L3U3 hp hQ) c.isL2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
