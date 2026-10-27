module

public import CFSG.RankThree.PartTwo.Sec15.Liebeck155R1T150SporCore
import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4KS219
import CFSG.RankThree.PartTwo.Sec4.RonanK429RowHComp
public import CFSG.Sporadic.J4

public section

namespace CFSG.RankThree.PartTwo.Sec15.Liebeck155R1T150

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem k150s_j4 {J : Type} [Group J] (hJ : K150sTgt J) :
    RowOfK150 J (Spor .J4) := by
  have := hJ.simple.toNontrivial
  refine k150s_row_of_native CFSG.Sporadic.Bridge.J4.nonempty_mulEquiv ?_
  intro S _ _ hs hna ⟨e⟩
  have := hs
  have hout : ¬ 3 ∣ Nat.card (Outer (Blueprint.NativeSporadic.Carrier .J4)) := by
    rw [CFSG.AGLEmbedding.card_outer_J4]
    norm_num
  have e' : S ≃* Blueprint.NativeSporadic.J4 := e
  have f : S ≃* ↥CFSG.Sporadic.J4.J :=
    e'.trans (CFSG.Sporadic.J4.seedEquiv CFSG.Sporadic.J4.j4Facts.mat)
  refine @k150s_noCfg_of_model J _ S ↥CFSG.Sporadic.J4.J _ (Subgroup.toGroup _) f
    (RonanK429H.center_eq_bot_of_simple_nonab hna)
    (RonanK429H.not_three_dvd_outer_of_mulEquiv e hout) ?_
  intro y hy
  have hy3 : y ^ 3 = 1 := by
    rw [← hy]
    exact pow_orderOf_eq_one y
  have hy1 : y ≠ 1 := by
    rintro rfl
    simp at hy
  exact k150s_goodFor_of_isQuasisimple_centralizer hy
    (CFSG.AGLEmbeddingD2.Wilson.NormalizerAction.centralizer_data_J CFSG.Sporadic.J4.j4Facts y
      hy3 hy1).1

end CFSG.RankThree.PartTwo.Sec15.Liebeck155R1T150
