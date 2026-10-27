module

public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowVTools
public import CFSG.RankThree.PartTwo.Sec4.Item426A6U43
public import CFSG.RankThree.PartTwo.Sec4.Item47Unitary
public import CFSG.Models.PGLOrders

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.KFacts
open CFSG.Assembly.RankThreeEven (projSU)

namespace RowV

theorem card_centralizer_u43_dvd (x : projSU 4 3 1) (hx : orderOf x = 3) :
    Nat.card (Subgroup.centralizer ({x} : Set (projSU 4 3 1))) ∣ 653184 := by
  have h5 := Item426.u43ThreeCentralizer x hx
  have hd : Nat.card (Subgroup.centralizer ({x} : Set (projSU 4 3 1))) ∣ 5 * 653184 := by
    rw [show 5 * 653184 = 3265920 by norm_num, ← CFSG.PGLModel.card_projSU_four_three]
    exact Subgroup.card_subgroup_dvd_card _
  exact (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_five).mpr h5)).dvd_of_dvd_mul_left
    hd

theorem noCfgS429_projSU_four_three {S : Type} [Group S] [Finite S] (hs : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (φ : S ≃* projSU 4 3 1) : NoCfgS429 S := by
  refine noCfgS429_of_inner (N := 653184) (B := 7) (center_eq_bot_of_simple hs hna) ?_ ?_
    (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro τ h3
    have h3' : MulAut.congr φ τ ^ 3 = 1 := by rw [← map_pow, h3, map_one]
    exact (isInnerAut_congr φ τ).mp (cubeInner_of_not_three_dvd_card_outer outU43_holds _ h3')
  · intro x hx
    rw [card_centralizer_congr φ x]
    exact card_centralizer_u43_dvd (φ x) (by rw [MulEquiv.orderOf_eq]; exact hx)

end RowV

end CFSG.RankThree.PartTwo.Sec4.RonanK429
