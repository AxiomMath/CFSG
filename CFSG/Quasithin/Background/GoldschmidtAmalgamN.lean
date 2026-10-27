module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamNSmall
public import CFSG.Quasithin.Background.GoldschmidtAmalgamNEight
public import CFSG.Quasithin.Background.GoldschmidtAmalgamNSixteen
public import CFSG.Quasithin.Background.GoldschmidtAmalgamSplit

public section

universe u

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

namespace F6

namespace GoldAmN

variable {D : Type*} [Group D] [Finite D] {G₁ G₂ : Subgroup D}

theorem isGoldCaseCat_of_not_charTwo_right (h : IsGoldschmidtAmalgam G₁ G₂)
    (hnc : ¬ CharTwo G₂) : IsGoldCaseCat G₁ G₂ := by
  obtain ⟨x, hx⟩ := exists_centThree G₂ h.quotient₂ hnc
  have hT' := h.toIsGoldschmidtTriple
  have hQ₁ := card_pCoreOf_left_le_eight h hx
  have hTcard := card_inf_eq_two_mul_left hT'
  obtain ⟨a, ha⟩ := exists_card_inf_eq hT'
  have hQpos : 0 < Nat.card ↥(pCoreOf 2 G₁) := Nat.card_pos
  have ha4 : a ≤ 4 := by
    by_contra hlt
    push Not at hlt
    have h5 : 2 ^ 5 ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) hlt
    have h32 : 32 ≤ Nat.card ↥(G₁ ⊓ G₂) := by rw [ha]; simpa using h5
    omega
  interval_cases a
  · exfalso
    rw [pow_zero] at ha
    omega
  · exact Or.inl (Or.inl (isGoldCaseI_of_card_two h (by simpa using ha)))
  · exact Or.inl (Or.inr (Or.inl (isGoldCaseII_of_card_four h (by simpa using ha))))
  · exact isGoldCaseCat_of_card_eight h hx (by simpa using ha)
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (isGoldCaseV_of_card_sixteen h hx (by simpa using ha)))))))

end GoldAmN

theorem goldschmidtNonCharTwoList_holds : GoldschmidtNonCharTwoList.{u} := by
  intro D _ _ G₁ G₂ h hnot
  by_cases hc : CharTwo G₂
  · have hc₁ : ¬ CharTwo G₁ := fun h1 => hnot ⟨h1, hc⟩
    exact isGoldCaseCat_comm.mp
      (GoldAmN.isGoldCaseCat_of_not_charTwo_right (GoldAmN.amalgam_symm h) hc₁)
  · exact GoldAmN.isGoldCaseCat_of_not_charTwo_right h hc

end F6

end CFSG.Quasithin
