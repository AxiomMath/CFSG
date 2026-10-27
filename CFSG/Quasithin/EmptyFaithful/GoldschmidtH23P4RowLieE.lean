module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4RowLieD
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4OutAlt
public import CFSG.Quasithin.Background.FLcSL

public section

namespace CFSG.Quasithin.H23P4

open CFSG.Assembly.LowTwoRank

theorem rowOK_of_isPSL_two {n : ℕ} (hn : 1 ≤ n) {X : Type} [Group X] [Finite X]
    (h : IsPSL n 2 1 X) : RowOK X where
  center := (CFSG.RankThree.PartOne.Sec109.lnTwoOuter X n h).1
  out := CFSG.Quasithin.H23Out.out5Pow_of_isPSL_two h
  idx := by
    obtain ⟨e⟩ := CFSG.Quasithin.FLc.nonempty_equiv_SLt_of_isPSL h
    exact NoFiveIndex.of_mulEquiv e (noFiveIndex_specialLinear_two hn)

theorem rowOK_of_isPSL_four_two {X : Type} [Group X] [Finite X] (h : IsPSL 4 2 1 X) : RowOK X :=
  rowOK_of_isPSL_two (by norm_num) h

theorem rowOK_of_isPSL_five_two {X : Type} [Group X] [Finite X] (h : IsPSL 5 2 1 X) : RowOK X :=
  rowOK_of_isPSL_two (by norm_num) h

theorem rowOK_statedSL_three_two : RowOK ↥(StatedSL 3 (ZMod 2)) := by
  let e := specialLinearGroupEquivStatedSL 3 (ZMod 2)
  refine ⟨?_, CFSG.Quasithin.H23Out.out5Pow_statedSL_three_two, ?_⟩
  · rw [← Subgroup.map_center_eq e, center_eq_bot_specialLinear_two (by norm_num),
      Subgroup.map_bot]
  · exact NoFiveIndex.of_mulEquiv e.symm (noFiveIndex_specialLinear_two (by norm_num))

end CFSG.Quasithin.H23P4
