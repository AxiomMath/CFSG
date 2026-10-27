module

public import CFSG.RankThree.PartTwo.Sec4.RonanEpsOrders
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherL62
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherL72
public import CFSG.Models.PGLOrders
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIVO8p
public import CFSG.RankThree.PartTwo.Sec19.Step1911Proof

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanEps

open CFSG.Assembly.RankThreeEven (projSL projSU projSp projOmegaPlus projOmegaMinus)

theorem card_projSU_five_two_gf2 : Nat.card (projSU 5 2 1) = 13685760 := by
  rw [CFSG.RankThree.PartTwo.Sec21.card_projSU (m := 5) (b := 1) (by norm_num) le_rfl]
  decide +kernel

theorem card_projSU_six_two_gf2 : Nat.card (projSU 6 2 1) = 9196830720 := by
  rw [CFSG.RankThree.PartTwo.Sec21.card_projSU (m := 6) (b := 1) (by norm_num) le_rfl]
  decide +kernel

theorem card_projSL_six_two_gf2 : Nat.card (projSL 6 (GaloisField 2 1)) = 20158709760 := by
  rw [← Nat.card_congr
    (CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoOther.slEquivProjSL (by norm_num : 1 ≤ 6)).toEquiv,
    CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoOther.L62.card_SL6]

theorem card_projSL_seven_two_gf2 : Nat.card (projSL 7 (GaloisField 2 1)) = 163849992929280 := by
  rw [← Nat.card_congr
    (CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoOther.slEquivProjSL (by norm_num : 1 ≤ 7)).toEquiv,
    CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoOther.L72.card_SL7]

theorem card_projSp_three_two_gf2 : Nat.card (projSp 3 (GaloisField 2 1)) = 1451520 :=
  CFSG.PGLModel.card_projSp_three_two

theorem card_projSp_four_two_gf2 : Nat.card (projSp 4 (GaloisField 2 1)) = 47377612800 := by
  rw [CFSG.PGLModel.card_projSp_of_charTwo, GaloisField.card 2 1 (by norm_num)]
  decide +kernel

theorem card_projOmegaPlus_four_two_gf2 :
    Nat.card (projOmegaPlus 4 (GaloisField 2 1)) = 174182400 := by
  have hm : CFSG.Open.StatedClassicalModel (projOmegaPlus 4 (GaloisField 2 1)) .POmegaPlus 4 2 1 :=
    ⟨⟨Nat.prime_two, le_rfl, le_refl 4⟩, GaloisField 2 1, inferInstance, inferInstance,
      GaloisField.card 2 1 one_ne_zero,
      ⟨CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIV.statedOmegaPlusEquiv.symm⟩⟩
  rw [(CFSG.Timmesfeld.card_statedClassicalModel_two hm).2.2.2.1 rfl]
  decide +kernel

theorem card_projOmegaMinus_four_two_gf2 {b c : GaloisField 2 1}
    (hbc : ∀ s : GaloisField 2 1, s ^ 2 + b * s + c ≠ 0) :
    Nat.card (projOmegaMinus 3 (GaloisField 2 1) b c) = 197406720 := by
  rw [CFSG.RankThree.PartTwo.Sec19.Step1911Proof.card_projOmegaMinus hbc]
  decide +kernel

theorem rowSEpsOf_eight_SU5 : RowSEpsOf (projSU 5 2 1) := by
  intro S _ _ _ _ ⟨e⟩
  exact noCfgSEps_of_card (N := 13685760) (B := 3)
    (by rw [Nat.card_congr e.toEquiv, card_projSU_five_two_gf2]) (by norm_num) (by norm_num)
    (by decide +kernel) (by decide +kernel)

theorem rowSEpsOf_eight_SL6 : RowSEpsOf (projSL 6 (GaloisField 2 1)) := by
  intro S _ _ _ _ ⟨e⟩
  exact noCfgSEps_of_card (N := 20158709760) (B := 3)
    (by rw [Nat.card_congr e.toEquiv, card_projSL_six_two_gf2]) (by norm_num) (by norm_num)
    (by decide +kernel) (by decide +kernel)

theorem rowSEpsOf_eight_SU6 : RowSEpsOf (projSU 6 2 1) := by
  intro S _ _ _ _ ⟨e⟩
  exact noCfgSEps_of_card (N := 9196830720) (B := 3)
    (by rw [Nat.card_congr e.toEquiv, card_projSU_six_two_gf2]) (by norm_num) (by norm_num)
    (by decide +kernel) (by decide +kernel)

theorem rowSEpsOf_eight_SL7 : RowSEpsOf (projSL 7 (GaloisField 2 1)) := by
  intro S _ _ _ _ ⟨e⟩
  exact noCfgSEps_of_card (N := 163849992929280) (B := 4)
    (by rw [Nat.card_congr e.toEquiv, card_projSL_seven_two_gf2]) (by norm_num) (by norm_num)
    (by decide +kernel) (by decide +kernel)

theorem rowSEpsOf_eight_Sp6 : RowSEpsOf (projSp 3 (GaloisField 2 1)) := by
  intro S _ _ _ _ ⟨e⟩
  exact noCfgSEps_of_card (N := 1451520) (B := 3)
    (by rw [Nat.card_congr e.toEquiv, card_projSp_three_two_gf2]) (by norm_num) (by norm_num)
    (by decide +kernel) (by decide +kernel)

theorem rowSEpsOf_eight_Sp8 : RowSEpsOf (projSp 4 (GaloisField 2 1)) := by
  intro S _ _ _ _ ⟨e⟩
  exact noCfgSEps_of_card (N := 47377612800) (B := 3)
    (by rw [Nat.card_congr e.toEquiv, card_projSp_four_two_gf2]) (by norm_num) (by norm_num)
    (by decide +kernel) (by decide +kernel)

theorem rowSEpsOf_eight_OmegaPlus : RowSEpsOf (projOmegaPlus 4 (GaloisField 2 1)) := by
  intro S _ _ _ _ ⟨e⟩
  exact noCfgSEps_of_card (N := 174182400) (B := 3)
    (by rw [Nat.card_congr e.toEquiv, card_projOmegaPlus_four_two_gf2]) (by norm_num) (by norm_num)
    (by decide +kernel) (by decide +kernel)

theorem rowSEpsOf_eight_OmegaMinus : ∀ b c : GaloisField 2 1,
    (∀ s : GaloisField 2 1, s ^ 2 + b * s + c ≠ 0) →
      RowSEpsOf (projOmegaMinus 3 (GaloisField 2 1) b c) := by
  intro b c hbc S _ _ _ _ ⟨e⟩
  exact noCfgSEps_of_card (N := 197406720) (B := 3)
    (by rw [Nat.card_congr e.toEquiv, card_projOmegaMinus_four_two_gf2 hbc]) (by norm_num)
    (by norm_num) (by decide +kernel) (by decide +kernel)

end CFSG.RankThree.PartTwo.Sec4.RonanEps
