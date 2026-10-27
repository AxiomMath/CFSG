module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K332RowsDef
import CFSG.LocalAnalysis.UniquenessCase.UC6K332FamSp6
import CFSG.LocalAnalysis.UniquenessCase.UC6K332FamPsu
import CFSG.LocalAnalysis.UniquenessCase.UC6K332FamPsl
import CFSG.LocalAnalysis.UniquenessCase.UC6K332OuterLin
import CFSG.LocalAnalysis.UniquenessCase.UC6K332OuterUni

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.K332Route

open CFSG.Blueprint (LieModel)
open CFSG.RankThree.PartTwo.Sec4.RonanK432 (ListRow OuterRow)

structure K332RowsRest : Prop where
  list_trialityD4 : ∀ (S : Type) [Group S] [Finite S] (p f : ℕ), LieModel S .trialityD4 0 p f →
    p ≠ 2 → p ≠ 3 → ListRow S
  outer_trialityD4 : ∀ (S : Type) [Group S] [Finite S] (p f : ℕ), LieModel S .trialityD4 0 p f →
    p ≠ 2 → p ≠ 3 → OuterRow S
  list_pomegaMinus8 : ∀ (S : Type) [Group S] [Finite S] (p f : ℕ), LieModel S .POmegaMinus 4 p f →
    p ≠ 3 → ListRow S
  outer_pomegaMinus8 : ∀ (S : Type) [Group S] [Finite S] (p f : ℕ), LieModel S .POmegaMinus 4 p f →
    p ≠ 3 → OuterRow S
  list_pomegaOdd7 : ∀ (S : Type) [Group S] [Finite S] (p f : ℕ), LieModel S .POmegaOdd 3 p f →
    p ≠ 3 → ListRow S
  outer_pomegaOdd7 : ∀ (S : Type) [Group S] [Finite S] (p f : ℕ), LieModel S .POmegaOdd 3 p f →
    p ≠ 3 → OuterRow S

theorem k332Rows_of_rest (hR : K332RowsRest) : K332Rows where
  list_trialityD4 := hR.list_trialityD4
  outer_trialityD4 := hR.outer_trialityD4
  outer_psl4 := outerRow_psl4_of_two_le
  outer_psu4 := outerRow_psu4_of_two_le
  list_psu5 := listRow_psu5
  outer_psu5 := outerRow_psu5
  list_psp6 := listRow_psp6
  outer_psp6 := outerRow_psp6
  list_pomegaMinus8 := hR.list_pomegaMinus8
  outer_pomegaMinus8 := hR.outer_pomegaMinus8
  list_pomegaOdd7 := hR.list_pomegaOdd7
  outer_pomegaOdd7 := hR.outer_pomegaOdd7
  list_psl6 := listRow_psl6
  outer_psl6 := outerRow_psl6
  list_psu6 := listRow_psu6
  outer_psu6 := outerRow_psu6
  list_psl7 := listRow_psl7
  outer_psl7 := outerRow_psl7
  list_psu7 := listRow_psu7
  outer_psu7 := outerRow_psu7

end CFSG.LocalAnalysis.UniquenessCase.UCK.K332Route
