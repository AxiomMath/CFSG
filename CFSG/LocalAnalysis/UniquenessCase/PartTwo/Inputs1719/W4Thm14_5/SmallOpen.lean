module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallRows
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallL2
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallSL3
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallSp4
import CFSG.LocalAnalysis.UniquenessCase.UC22P22rk

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 Subgroup
open CFSG.Blueprint (LieModel)

theorem isSL3_of_isL3 {A : Type} [Group A] {e : ℕ} (hq : CFSG.Open.IsQuasisimple A)
    (h : IsL3 A e) : IsSL3 A e := by
  have := uc22p22r_lieModel_isSimple_classical (Or.inl rfl) h
  have hZ := center_eq_bot_of_isQuasisimple hq
  exact ⟨hq, LieModel.of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm h⟩

theorem k14_5SmallFor_l3 :
    K14_5SmallFor fun L _ e => IsL3 L e :=
  K14_5SmallFor.mono (fun _ _ _ hq h => isSL3_of_isL3 hq h) k14_5SmallFor_sl3

structure K14_5SmallOpen : Prop where
  u4 : K14_5SmallFor fun L _ e => IsU4 L e
  g2 : K14_5SmallFor fun L _ e => IsG2 L e
  d4 : K14_5SmallFor fun L _ e => Is3D4 L e
  f4 : K14_5SmallFor fun L _ e => LieModel L .twistedF4 0 2 e
  u5 : K14_5SmallFor fun L _ e => e = 2 ∧ IsU5 L 2
  l4 : K14_5SmallFor fun L _ e => LieModel L .PSL 4 2 e
  sp6 : K14_5SmallFor fun L _ e => LieModel L .PSp 3 2 e
  o8m : K14_5SmallFor fun L _ e => IsOmega8m L e

theorem k14_5Small_of_open
    (h : K14_5SmallOpen) :
    K14_5Small :=
  k14_5Small_of_rows k14_5SmallFor_l2 k14_5SmallFor_sz k14_5SmallFor_u3 k14_5SmallFor_su3
    k14_5SmallFor_l3 k14_5SmallFor_sl3 k14_5SmallFor_sp4 h.u4 h.g2 h.d4 h.f4 h.u5 h.l4 h.sp6
    h.o8m

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
