module

public import CFSG.RankThree.PartTwo.Sec21.FF79KFacts14
import CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194Mult
import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCenter

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG CFSG.RankThree.PartTwo.Sec21
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.LieType.Steinberg.CentralExt.GriessClassical

theorem card_center_dvd_two_of_typeLn
    {Y : Type} [Group Y] [Finite Y] (hY : CFSG.IsQuasisimple Y)
    {n : ℕ} (hn : n = 4 ∨ n = 5)
    (hm : StatedClassicalModel (Y ⧸ Subgroup.center Y) .PSL n 2 1) :
    Nat.card (Subgroup.center Y) ∣ 2 := by
  rcases hn with rfl | rfl
  · have hG : Nat.card (CFSG.Blueprint.Multiplier.generic .PSL 4 2 1 ×
        CFSG.Blueprint.Multiplier.exceptional .PSL 4 2 1) = 2 := by
      have hg : CFSG.Blueprint.Multiplier.genericOrders .PSL 4 2 1 = (1, 1) := by decide
      have he : CFSG.Blueprint.Multiplier.exceptionalOrders .PSL 4 2 1 = (2, 1) := by decide
      simp only [CFSG.Blueprint.Multiplier.generic, CFSG.Blueprint.Multiplier.exceptional, hg, he,
        Nat.card_prod, Nat.card_zmod, Nat.card_congr Multiplicative.ofAdd.symm]
    exact CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194.card_center_dvd_of_row hY
      (MulEquiv.refl _) (psl_row hm).2 hG
  · have hL : CFSG.Blueprint.LieModel (Y ⧸ Subgroup.center Y) .PSL 5 2 1 :=
      .inl ⟨by decide, hm⟩
    have hZ := CFSG.OddStandard.SmallF3.HypA2Leaves.a2l_center_eq_bot_psl52 hY hL
    rw [hZ, Subgroup.card_bot]
    exact one_dvd 2

theorem ff79KCenterJ_holds :
    FF79KCenterJ := by
  intro G _ _ n J hn hq hm
  exact card_center_dvd_two_of_typeLn hq hn hm

end CFSG.RankThree.PartTwo.Sec21.FF79
