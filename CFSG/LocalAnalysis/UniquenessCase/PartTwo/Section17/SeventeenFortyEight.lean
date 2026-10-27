module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsC

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem p17_42_more_two_iff (D : Data G) (X : Subgroup G) :
    P17_42_more D X 2 ↔ evenRank G = 3 := by
  constructor
  · exact fun h => h.1
  · intro h
    refine ⟨h, ?_⟩
    intro r hr h5 hdvd
    rw [show 2 ^ 2 - 1 = 3 by norm_num] at hdvd
    have hle : r ≤ 3 := Nat.le_of_dvd (by norm_num) hdvd
    omega


theorem p17_42_three_of_isU5_two {D : Data G} {X : Subgroup G} {p : ℕ}
    (hU5 : IsU5 (Bar2 X) 2) (hk : D.k = 2) (hp5 : p = 5) (he : evenRank G = 3) :
    P17_42_3 D X p := by
  exact ⟨2, hU5, rfl, hk, hp5, (p17_42_more_two_iff D X).mpr he⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17