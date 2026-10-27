module

public import CFSG.Adapters.LieModelOrders
public import CFSG.LocalAnalysis.UniquenessCase.UCFront09

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC22.F09 (Inv9)
open CFSG.LocalAnalysis.RankThreeUC (uniqueSet)

variable {G : Type} [Group G] [Finite G]

theorem s16h_e3_omega_card_of_isL2 {X : Type} [Group X] {f : ℕ} (h : IsL2 X f) :
    Nat.card X = ordA 1 (2 ^ f) :=
  (CFSG.Blueprint.LieModel.card_eq_lieOrd (by norm_num) h).trans rfl

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
