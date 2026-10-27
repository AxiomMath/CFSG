module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.K332Route

open CFSG.Blueprint (LieModel)
open CFSG.RankThree.PartTwo.Sec4.RonanK432 (ListRow OuterRow)

structure K332Rows : Prop where
  list_trialityD4 : ∀ (S : Type) [Group S] [Finite S] (p f : ℕ), LieModel S .trialityD4 0 p f →
    p ≠ 2 → p ≠ 3 → ListRow S
  outer_trialityD4 : ∀ (S : Type) [Group S] [Finite S] (p f : ℕ), LieModel S .trialityD4 0 p f →
    p ≠ 2 → p ≠ 3 → OuterRow S
  outer_psl4 : ∀ (S : Type) [Group S] [Finite S] (p f : ℕ), LieModel S .PSL 4 p f → p ≠ 3 → 2 ≤ f →
    OuterRow S
  outer_psu4 : ∀ (S : Type) [Group S] [Finite S] (p f : ℕ), LieModel S .PSU 4 p f → p ≠ 2 → p ≠ 3 →
    2 ≤ f → OuterRow S
  list_psu5 : ∀ (S : Type) [Group S] [Finite S] (p f : ℕ), LieModel S .PSU 5 p f → p ^ f % 3 = 1 →
    ListRow S
  outer_psu5 : ∀ (S : Type) [Group S] [Finite S] (p f : ℕ), LieModel S .PSU 5 p f → p ^ f % 3 = 1 →
    OuterRow S
  list_psp6 : ∀ (S : Type) [Group S] [Finite S] (p f : ℕ), LieModel S .PSp 3 p f → p ≠ 3 → ListRow S
  outer_psp6 : ∀ (S : Type) [Group S] [Finite S] (p f : ℕ), LieModel S .PSp 3 p f → p ≠ 3 →
    OuterRow S
  list_pomegaMinus8 : ∀ (S : Type) [Group S] [Finite S] (p f : ℕ), LieModel S .POmegaMinus 4 p f →
    p ≠ 3 → ListRow S
  outer_pomegaMinus8 : ∀ (S : Type) [Group S] [Finite S] (p f : ℕ), LieModel S .POmegaMinus 4 p f →
    p ≠ 3 → OuterRow S
  list_pomegaOdd7 : ∀ (S : Type) [Group S] [Finite S] (p f : ℕ), LieModel S .POmegaOdd 3 p f →
    p ≠ 3 → ListRow S
  outer_pomegaOdd7 : ∀ (S : Type) [Group S] [Finite S] (p f : ℕ), LieModel S .POmegaOdd 3 p f →
    p ≠ 3 → OuterRow S
  list_psl6 : ∀ (S : Type) [Group S] [Finite S] (p f : ℕ), LieModel S .PSL 6 p f → p ^ f % 3 = 2 →
    ListRow S
  outer_psl6 : ∀ (S : Type) [Group S] [Finite S] (p f : ℕ), LieModel S .PSL 6 p f → p ^ f % 3 = 2 →
    OuterRow S
  list_psu6 : ∀ (S : Type) [Group S] [Finite S] (p f : ℕ), LieModel S .PSU 6 p f → p ^ f % 3 = 1 →
    ListRow S
  outer_psu6 : ∀ (S : Type) [Group S] [Finite S] (p f : ℕ), LieModel S .PSU 6 p f → p ^ f % 3 = 1 →
    OuterRow S
  list_psl7 : ∀ (S : Type) [Group S] [Finite S] (p f : ℕ), LieModel S .PSL 7 p f → p ^ f % 3 = 2 →
    ListRow S
  outer_psl7 : ∀ (S : Type) [Group S] [Finite S] (p f : ℕ), LieModel S .PSL 7 p f → p ^ f % 3 = 2 →
    OuterRow S
  list_psu7 : ∀ (S : Type) [Group S] [Finite S] (p f : ℕ), LieModel S .PSU 7 p f → p ^ f % 3 = 1 →
    ListRow S
  outer_psu7 : ∀ (S : Type) [Group S] [Finite S] (p f : ℕ), LieModel S .PSU 7 p f → p ^ f % 3 = 1 →
    OuterRow S

end CFSG.LocalAnalysis.UniquenessCase.UCK.K332Route
