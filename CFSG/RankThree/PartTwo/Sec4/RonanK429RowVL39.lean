module

public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowVOrders
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowVL39Lin
public import CFSG.RankThree.PartTwo.Sec4.Item49Small

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.KFacts
open CFSG.Assembly.RankThreeEven (projSL)

namespace RowV

theorem card_centralizer_l39_dvd (x : projSL 3 (GaloisField 3 2)) (hx : orderOf x = 3) :
    Nat.card (Subgroup.centralizer ({x} : Set (projSL 3 (GaloisField 3 2)))) ∣ 6065280 := by
  have h7 := l39_not_seven_dvd_card_centralizer x hx
  have hd : Nat.card (Subgroup.centralizer ({x} : Set (projSL 3 (GaloisField 3 2)))) ∣
      7 * 6065280 := by
    have hS := card_projSL_three_char_three (e := 2) (by norm_num)
    norm_num at hS
    rw [show 7 * 6065280 = 42456960 by norm_num, ← hS]
    exact Subgroup.card_subgroup_dvd_card _
  exact (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr h7)).dvd_of_dvd_mul_left
    hd

theorem noCfgS429_projSL_three_nine {S : Type} [Group S] [Finite S] (hs : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (φ : S ≃* projSL 3 (GaloisField 3 2)) : NoCfgS429 S := by
  refine noCfgS429_of_inner (N := 6065280) (B := 9) (center_eq_bot_of_simple hs hna) ?_ ?_
    (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro τ h3
    have h3' : MulAut.congr φ τ ^ 3 = 1 := by rw [← map_pow, h3, map_one]
    exact (isInnerAut_congr φ τ).mp (cubeInner_of_not_three_dvd_card_outer
      (Item49Small.not_three_dvd_card_outer_projSL (by norm_num) (by norm_num) (by decide)) _ h3')
  · intro x hx
    rw [card_centralizer_congr φ x]
    exact card_centralizer_l39_dvd (φ x) (by rw [MulEquiv.orderOf_eq]; exact hx)

end RowV

end CFSG.RankThree.PartTwo.Sec4.RonanK429
