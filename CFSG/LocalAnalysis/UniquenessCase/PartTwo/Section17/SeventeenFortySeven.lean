module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P21k

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem isSL3_of_isL3_barInf {D : Data G} {L : Subgroup G} {n : ℕ} (hL : L ∈ calC D.M)
    (h : IsL3 (BarInf L) n) : IsSL3 (Bar2 L) n := by
  obtain ⟨e⟩ := CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p21k_barInf_equiv_of_calC hL
  exact ⟨hL.2.2, CFSG.Blueprint.LieModel.of_mulEquiv e h⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
