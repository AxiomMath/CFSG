module

public import CFSG.RankThree.PartTwo.Sec4.Ronan431Open
public import CFSG.RankThree.PartTwo.Sec4.Ronan431E81Lie
public import CFSG.RankThree.PartTwo.Sec4.Ronan431E81Alt
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIVTorus

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan431E81

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.Ronan431
open CFSG.Assembly.RankThreeEven (projSL projSU projSp projOmegaPlus)

theorem rowSOf431_sl2_three_of_four_le (e : ℕ) (he : 4 ≤ e) :
    RowSOf431 (projSL 2 (GaloisField 3 e)) :=
  rowSOf431_of_three_lt_pRank (three_lt_pRank_projSL_two_three he)

theorem rowSOf431_sl3_nine : RowSOf431 (projSL 3 (GaloisField 3 2)) :=
  rowSOf431_of_three_lt_pRank three_lt_pRank_projSL_three_nine

theorem rowSOf431_su3_nine : RowSOf431 (projSU 3 3 2) := by
  obtain ⟨E, hE, h81⟩ := exists_e81_projSU_three_nine
  exact rowSOf431_of_elemAbelian hE h81.ge

theorem rowSOf431_sl4_three : RowSOf431 (projSL 4 (GaloisField 3 1)) := by
  refine rowSOf431_of_three_lt_pRank ?_
  have h := Census.le_pRank_projSL_four (GaloisField 3 1) (p := 3) (k := 1)
    (GaloisField.card 3 1 (by norm_num))
  omega

theorem rowSOf431_su5_two : RowSOf431 (projSU 5 2 1) := by
  obtain ⟨E, hE, h81⟩ := Item434SmallTwoIV.exists_elemAbelian_projSU_torus 4 2 1 le_rfl
    (by norm_num) (by norm_num)
  exact rowSOf431_of_elemAbelian hE (by rw [h81]; norm_num)

theorem rowSOf431_su5_eight : RowSOf431 (projSU 5 2 3) := by
  obtain ⟨E, hE, h81⟩ := Item434SmallTwoIV.exists_elemAbelian_projSU_torus 4 2 3 (by norm_num)
    (by norm_num) (by norm_num)
  exact rowSOf431_of_elemAbelian hE (by rw [h81]; norm_num)

theorem rowSOf431_su6_two : RowSOf431 (projSU 6 2 1) :=
  rowSOf431_of_three_lt_pRank Census.three_lt_pRank_projSU_six_two

theorem rowSOf431_sp8_two : RowSOf431 (projSp 4 (GaloisField 2 1)) := by
  obtain ⟨E, hE, h81⟩ := exists_e81_projSp (K := GaloisField 2 1) (n := 4) le_rfl
  exact rowSOf431_of_elemAbelian hE h81.ge

theorem rowSOf431_omegaPlus8_two : RowSOf431 (projOmegaPlus 4 (GaloisField 2 1)) :=
  rowSOf431_of_three_lt_pRank Census.three_lt_pRank_omegaPlus

theorem rowSOf431_alt12 : RowSOf431 (alternatingGroup (Fin 12)) := by
  obtain ⟨E, hE, h81⟩ := exists_e81_alternatingGroup_twelve
  exact rowSOf431_of_elemAbelian hE h81.ge

theorem rowSOf431_spor_mcl :
    RowSOf431 (Spor .McL) :=
  rowSOf431_of_three_lt_pRank Census.SporadicTwoCover.three_lt_pRank_mcl

theorem rowSOf431_spor_ly :
    RowSOf431 (Spor .Ly) :=
  rowSOf431_of_three_lt_pRank Census.SporadicTwoCover.three_lt_pRank_ly

theorem rowSOf431_spor_co2 :
    RowSOf431 (Spor .Co2) :=
  rowSOf431_of_three_lt_pRank Census.SporadicTwoCover.three_lt_pRank_co2

theorem rowSOf431_spor_co3 :
    RowSOf431 (Spor .Co3) :=
  rowSOf431_of_three_lt_pRank Census.SporadicTwoCover.three_lt_pRank_co3

theorem rowSOf431_spor_hn :
    RowSOf431 (Spor .HN) :=
  rowSOf431_of_three_lt_pRank Census.SporadicTwoCover.three_lt_pRank_hn

theorem rowSOf431_spor_th :
    RowSOf431 (Spor .Th) :=
  rowSOf431_of_three_lt_pRank Census.SporadicTwoCover.three_lt_pRank_th

theorem rowSOf431_spor_onan :
    RowSOf431 (Spor .ONan) :=
  rowSOf431_of_three_lt_pRank Census.SporadicTwoCover.three_lt_pRank_onan

theorem rowSOf431_spor_suz :
    RowSOf431 (Spor .Suz) :=
  rowSOf431_of_three_lt_pRank Census.three_lt_pRank_suz

theorem k431OpenB :
    K431OpenB where
  one_ge4 := rowSOf431_sl2_three_of_four_le
  five_twelve := rowSOf431_alt12
  six_McL := rowSOf431_spor_mcl
  six_Ly := rowSOf431_spor_ly
  six_Suz := rowSOf431_spor_suz
  six_ONan := rowSOf431_spor_onan
  six_Co3 := rowSOf431_spor_co3
  six_Co2 := rowSOf431_spor_co2
  six_HN := rowSOf431_spor_hn
  six_Th := rowSOf431_spor_th
  eight_SU5 := rowSOf431_su5_two
  eight_SU6 := rowSOf431_su6_two
  eight_Sp8 := rowSOf431_sp8_two
  eight_OmegaPlus := rowSOf431_omegaPlus8_two
  eight_SU5_8 := rowSOf431_su5_eight
  nine_SL3_nine := rowSOf431_sl3_nine
  nine_SU3_nine := rowSOf431_su3_nine
  nine_SL4 := rowSOf431_sl4_three

end CFSG.RankThree.PartTwo.Sec4.Ronan431E81
