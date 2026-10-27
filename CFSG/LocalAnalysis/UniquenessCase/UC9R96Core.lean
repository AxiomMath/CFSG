module

import CFSG.LocalAnalysis.UniquenessCase.UCFront09R912A5
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC9R96

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

structure Core (D : Data G) (Y H : Subgroup G) (q : ℕ) : Prop where
  Y_le_H : Y ≤ H
  Y_le_M : Y ≤ D.M
  not_H_le_M : ¬ H ≤ D.M
  H_ne_top : H ≠ ⊤
  prime : q.Prime
  gt : 5 < q
  shape_opp : IsL2Odd (Bar2 (Opp 3 Y)) q
  isSimpleGroup_bar2_opp : IsSimpleGroup (Bar2 (Opp 3 Y))
  three_dvd_card_bar2_opp : 3 ∣ Nat.card (Bar2 (Opp 3 Y))
  not_isSolvable_bar2_opp : ¬ Group.IsSolvable (Bar2 (Opp 3 Y))
  comm_le : ∀ A : Subgroup G, A ≤ H → A ≤ D.M → ¬ 3 ∣ Nat.card A →
    Opp 3 Y ≤ normalizer (A : Set G) → ⁅A, Opp 3 Y⁆ ≤ pCoreOf 2 A

namespace Core

variable {D : Data G} {Y H : Subgroup G} {q : ℕ}

theorem opp_le_H (S : Core D Y H q) : Opp 3 Y ≤ H := (F09.opp_le_self 3 Y).trans S.Y_le_H

theorem opp_le_M (S : Core D Y H q) : Opp 3 Y ≤ D.M := (F09.opp_le_self 3 Y).trans S.Y_le_M

end Core

end CFSG.LocalAnalysis.UniquenessCase.UC9R96
