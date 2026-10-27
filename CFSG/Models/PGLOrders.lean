module

public import CFSG.Models.PGL
public import CFSG.Adapters.StatedClassicalSmallOrders
public import CFSG.Adapters.StatedClassicalUnitaryOrders

public section

namespace CFSG.PGLModel

open CFSG.Open.StatedAPI

theorem card_projSL_three_four : Nat.card (projSL 3 (GaloisField 2 2)) = 20160 :=
  card_of_statedClassicalModel_psl_three_four
    (statedClassicalModel_of_mulEquiv_projSL
      ⟨Nat.prime_two, by norm_num, by norm_num, by decide, by decide⟩ (MulEquiv.refl _))

theorem card_projSL_two_sixteen : Nat.card (projSL 2 (GaloisField 2 4)) = 4080 :=
  card_of_statedClassicalModel_psl_two_sixteen
    (statedClassicalModel_of_mulEquiv_projSL
      ⟨Nat.prime_two, by norm_num, le_rfl, by decide, by decide⟩ (MulEquiv.refl _))

theorem card_projSU_three_three : Nat.card (projSU 3 3 1) = 6048 :=
  card_of_statedClassicalModel_psu_three_three
    (statedClassicalModel_of_mulEquiv_projSU ⟨Nat.prime_three, le_rfl, le_rfl, by decide⟩
      (MulEquiv.refl _))

theorem card_projSU_three_four : Nat.card (projSU 3 2 2) = 62400 :=
  card_of_statedClassicalModel_psu_three_four
    (statedClassicalModel_of_mulEquiv_projSU ⟨Nat.prime_two, by norm_num, le_rfl, by decide⟩
      (MulEquiv.refl _))

theorem card_projSU_three_five [Fact (Nat.Prime 5)] : Nat.card (projSU 3 5 1) = 126000 :=
  card_of_statedClassicalModel_psu_three_five
    (statedClassicalModel_of_mulEquiv_projSU ⟨Fact.out, le_rfl, le_rfl, by decide⟩
      (MulEquiv.refl _))

theorem card_projSU_three_eight : Nat.card (projSU 3 2 3) = 5515776 :=
  card_of_statedClassicalModel_psu_three_eight
    (statedClassicalModel_of_mulEquiv_projSU ⟨Nat.prime_two, by norm_num, le_rfl, by decide⟩
      (MulEquiv.refl _))

theorem card_projSU_four_two : Nat.card (projSU 4 2 1) = 25920 :=
  card_of_statedClassicalModel_psu_four_two
    (statedClassicalModel_of_mulEquiv_projSU ⟨Nat.prime_two, le_rfl, by norm_num, by decide⟩
      (MulEquiv.refl _))

theorem card_projSU_four_three : Nat.card (projSU 4 3 1) = 3265920 :=
  card_of_statedClassicalModel_psu_four_three
    (statedClassicalModel_of_mulEquiv_projSU ⟨Nat.prime_three, le_rfl, by norm_num, by decide⟩
      (MulEquiv.refl _))

theorem card_projSU_four_four : Nat.card (projSU 4 2 2) = 1018368000 :=
  card_of_statedClassicalModel_psu_four_four
    (statedClassicalModel_of_mulEquiv_projSU ⟨Nat.prime_two, by norm_num, by norm_num, by decide⟩
      (MulEquiv.refl _))

theorem card_projSU_five_four : Nat.card (projSU 5 2 2) = 53443952640000 :=
  card_of_statedClassicalModel_psu_five_four
    (statedClassicalModel_of_mulEquiv_projSU ⟨Nat.prime_two, by norm_num, by norm_num, by decide⟩
      (MulEquiv.refl _))

theorem card_projSp_of_charTwo (n : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2] :
    Nat.card (projSp n K) =
      Nat.card K ^ (n ^ 2) * ∏ j ∈ Finset.Icc 1 n, (Nat.card K ^ (2 * j) - 1) :=
  (Nat.card_congr (projSpEquivStatedProj n K).toEquiv).trans
    (CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSp_of_charTwo n)

theorem card_projSp_two_two : Nat.card (projSp 2 (GaloisField 2 1)) = 720 := by
  rw [card_projSp_of_charTwo, GaloisField.card 2 1 (by norm_num)]
  decide

theorem card_projSp_two_eight : Nat.card (projSp 2 (GaloisField 2 3)) = 1056706560 := by
  rw [card_projSp_of_charTwo, GaloisField.card 2 3 (by norm_num)]
  decide

theorem card_projSp_three_two : Nat.card (projSp 3 (GaloisField 2 1)) = 1451520 := by
  rw [card_projSp_of_charTwo, GaloisField.card 2 1 (by norm_num)]
  decide

end CFSG.PGLModel
