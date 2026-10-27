module

import CFSG.GH74.Orders.LieType
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.D2Coprime
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin
open CFSG.Blueprint (LieModel)

private theorem w107_not_three_pow_seven_dvd_prod (r : ℕ) (hr : r ≤ 11) :
    ¬ 3 ^ 7 ∣ ∏ i : Fin r, (2 ^ r - 2 ^ (i : ℕ)) := by
  interval_cases r <;> simp [Fin.prod_univ_succ]

theorem w107_twelve_le_rk {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {L : Subgroup (MulAut W)} (h : LieModel (↥L ⧸ Subgroup.center ↥L) .PSU 4 3 1)
    (hZ : 3 ∣ Nat.card (Subgroup.center ↥L)) : 12 ≤ rk W := by
  by_contra hle
  have hrk : rk W ≤ 11 := by omega
  have hcardQ : Nat.card (↥L ⧸ Subgroup.center ↥L) = 2 ^ 7 * 3 ^ 6 * 5 * 7 := by
    rw [CFSG.GH74.card_of_lieModel_PSU (n := 4) (p := 3) (f := 1)
      (by norm_num) (by norm_num) h]
    decide
  have hcardL : Nat.card ↥L =
      Nat.card (↥L ⧸ Subgroup.center ↥L) * Nat.card (Subgroup.center ↥L) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥L)
  have h3 : 3 ^ 7 ∣ Nat.card ↥L := by
    rw [hcardL, hcardQ, show (3 : ℕ) ^ 7 = 3 ^ 6 * 3 by norm_num]
    exact mul_dvd_mul (by norm_num) hZ
  have hdvd : Nat.card ↥L ∣ Nat.card (MulAut W) := Subgroup.card_subgroup_dvd_card L
  rw [CFSG.Quasithin.card_mulAut_eq hW] at hdvd
  exact w107_not_three_pow_seven_dvd_prod (rk W) hrk (dvd_trans h3 hdvd)

end CFSG.LocalAnalysis.WeakClosure81
