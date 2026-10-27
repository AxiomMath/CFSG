module

import CFSG.Adapters.LieModelSimple
import CFSG.LocalAnalysis.PreuniquenessRankFour.Helpers
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KGroupFactsL2Seven
public import CFSG.LocalAnalysis.UniquenessCase.UCFront09

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC9R96

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

@[expose] def R9_6At7 (D : Data G) : Prop :=
  ∀ Y H D₃ : Subgroup G, F09.Hyp91 D Y H D₃ → H ≠ ⊤ → Opp 3 Y ∈ calC (H ⊓ D.M) →
    IsL2Odd (Bar2 (Opp 3 Y)) 7 →
    (∀ A : Subgroup G, A ≤ Opp 3 Y → (Nat.card A).Prime → Odd (Nat.card A) →
      normalizer (A : Set G) ≤ D.M) → False

theorem ne_top_of_mem_calMOf (D : Data G) {Z N : Subgroup G} (hN : N ∈ calMOf Z) : N ≠ ⊤ := by
  haveI := D.standing.simple
  exact CFSG.PreuniquenessRankFour.Helpers.twoLocal_ne_top D.standing.nonab hN.1.1

structure Std96 (D : Data G) (Y H D₃ : Subgroup G) : Prop where
  hyp : F09.Hyp91 D Y H D₃
  ne_top : H ≠ ⊤
  calC : Opp 3 Y ∈ calC (H ⊓ D.M)
  seven : IsL2Odd (Bar2 (Opp 3 Y)) 7

namespace Std96

variable {D : Data G} {Y H D₃ : Subgroup G}

theorem Y_le_M (S : Std96 D Y H D₃) : Y ≤ D.M := S.hyp.1.1

theorem Y_le_H (S : Std96 D Y H D₃) : Y ≤ H := S.hyp.2.1.1

theorem not_H_le_M (S : Std96 D Y H D₃) : ¬ H ≤ D.M := S.hyp.2.1.2.1

theorem isSimpleGroup_bar2_opp (S : Std96 D Y H D₃) : IsSimpleGroup (Bar2 (Opp 3 Y)) :=
  CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (t := .PSL) (by decide) S.seven

theorem three_dvd_card_bar2_opp (S : Std96 D Y H D₃) : 3 ∣ Nat.card (Bar2 (Opp 3 Y)) := by
  rw [PartTwo.Inputs1719.card_of_isL2Odd_seven S.seven]
  norm_num

end Std96

end CFSG.LocalAnalysis.UniquenessCase.UC9R96
