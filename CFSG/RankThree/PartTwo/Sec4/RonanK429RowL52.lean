module

public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowTools
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowsS
public import CFSG.RankThree.PartTwo.Sec4.RonanK432RowL52

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projSL)

theorem noE27_projSL_five_two : NoE27 (projSL 5 (GaloisField 2 1)) := by
  haveI : Finite (projSL 5 (GaloisField 2 1)) :=
    Finite.of_equiv _ Res417Four.gl5EquivProjSL.toEquiv
  refine noE27_of_not_dvd ?_
  rw [← Nat.card_congr Res417Four.gl5EquivProjSL.toEquiv]
  exact RonanK432.not_27_dvd_card_gl5

theorem rowSOf429_eight_SL5 : RowSOf429 (projSL 5 (GaloisField 2 1)) :=
  rowSOf429_of_noCfg fun _ _ _ hs hna ⟨e⟩ => noCfgS429_of_autNoE27
    (autNoE27_of_mulEquiv_of_noE27 e hs hna
      (Item434SmallTwoOther.not_three_dvd_card_outer_projSL_gf2 (by norm_num))
      noE27_projSL_five_two)

end CFSG.RankThree.PartTwo.Sec4.RonanK429
