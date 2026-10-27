module

public import CFSG.Quasithin.Background.F6Amalgams
public import CFSG.Quasithin.Background.F6SQTK

public section

universe u

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

namespace F6

variable {D : Type*} [Group D]

@[expose] def IsGoldCaseAutM12Cat (H₁ H₂ : Subgroup D) : Prop :=
  IsYAmalgam IsAutM12 H₁ H₂ ∧ F112Convention H₁ H₂ ∧ QuotientPCoreIsL22 H₁ ∧
    QuotientPCoreIsL22 H₂ ∧
    IsExtensionWith ↥H₁ (DihedralGroup 6)
      (fun N => IsCentralProduct₂ ↥N (QuaternionGroup 2) (QuaternionGroup 2)) ∧
    Nat.card ↥(pCoreOf 2 H₁) = 2 ^ 6 ∧ Nat.card ↥(centerOf (pCoreOf 2 H₁)) = 2 ∧
    Nat.card ↥(pCoreOf 2 H₂) = 2 ^ 6

@[expose] def IsGoldCaseVICat (H₁ H₂ : Subgroup D) : Prop :=
  IsGoldCaseL32 H₁ H₂ ∨ IsGoldCaseSp42 H₁ H₂ ∨ IsGoldCaseG22 H₁ H₂ ∨
    IsGoldCaseG22Prime H₁ H₂ ∨ IsGoldCaseM12 H₁ H₂ ∨ IsGoldCaseAutM12Cat H₁ H₂

@[expose] def IsGoldCaseOrientedCat (H₁ H₂ : Subgroup D) : Prop :=
  IsGoldCaseI H₁ H₂ ∨ IsGoldCaseII H₁ H₂ ∨ IsGoldCaseIII H₁ H₂ ∨ IsGoldCaseIV H₁ H₂ ∨
    IsGoldCaseV H₁ H₂ ∨ IsGoldCaseVICat H₁ H₂

@[expose] def IsGoldCaseCat (H₁ H₂ : Subgroup D) : Prop :=
  IsGoldCaseOrientedCat H₁ H₂ ∨ IsGoldCaseOrientedCat H₂ H₁

theorem isGoldCaseCat_comm {H₁ H₂ : Subgroup D} : IsGoldCaseCat H₁ H₂ ↔ IsGoldCaseCat H₂ H₁ :=
  or_comm

end F6

@[expose] def F6.GoldschmidtS3ListCat : Prop :=
  ∀ (D : Type u) [Group D] [Finite D] (G₁ G₂ : Subgroup D), IsGoldschmidtAmalgam G₁ G₂ →
    F6.IsGoldCaseCat G₁ G₂

namespace F6

variable {D : Type*} [Group D]

theorem isGoldCaseCat_quotient_pCore (hlist : GoldschmidtS3ListCat.{u}) {D : Type u} [Group D]
    [Finite D] {G₁ G₂ : Subgroup D} (h : IsGoldschmidtTriple G₁ G₂) :
    IsGoldCaseCat (G₁.map (QuotientGroup.mk' (Open.pCore 2 D)))
      (G₂.map (QuotientGroup.mk' (Open.pCore 2 D))) :=
  hlist _ _ _ h.quotient_pCore

theorem isGoldCaseVICat_of_charTwo [Finite D] {H₁ H₂ : Subgroup D} (h : IsGoldCaseCat H₁ H₂)
    (h₁ : CharTwo H₁) (h₂ : CharTwo H₂) : IsGoldCaseVICat H₁ H₂ ∨ IsGoldCaseVICat H₂ H₁ := by
  rcases h with h | h
  · rcases h with h | h | h | h | h | h
    · rcases not_charTwo_of_isGoldCase_i_v (Or.inl h) with h' | h' <;> contradiction
    · rcases not_charTwo_of_isGoldCase_i_v (Or.inr (Or.inl h)) with h' | h' <;> contradiction
    · rcases not_charTwo_of_isGoldCase_i_v (Or.inr (Or.inr (Or.inl h))) with h' | h' <;>
        contradiction
    · rcases not_charTwo_of_isGoldCase_i_v (Or.inr (Or.inr (Or.inr (Or.inl h)))) with h' | h' <;>
        contradiction
    · rcases not_charTwo_of_isGoldCase_i_v (Or.inr (Or.inr (Or.inr (Or.inr h)))) with h' | h' <;>
        contradiction
    · exact Or.inl h
  · rcases h with h | h | h | h | h | h
    · rcases not_charTwo_of_isGoldCase_i_v (Or.inl h) with h' | h' <;> contradiction
    · rcases not_charTwo_of_isGoldCase_i_v (Or.inr (Or.inl h)) with h' | h' <;> contradiction
    · rcases not_charTwo_of_isGoldCase_i_v (Or.inr (Or.inr (Or.inl h))) with h' | h' <;>
        contradiction
    · rcases not_charTwo_of_isGoldCase_i_v (Or.inr (Or.inr (Or.inr (Or.inl h)))) with h' | h' <;>
        contradiction
    · rcases not_charTwo_of_isGoldCase_i_v (Or.inr (Or.inr (Or.inr (Or.inr h)))) with h' | h' <;>
        contradiction
    · exact Or.inr h

theorem atMostOneInvolution_of_card_eq_two {S : Subgroup D} (hS : Nat.card ↥S = 2) :
    AtMostOneInvolution S :=
  fun _ hx _ hy _ _ hx1 hy1 => eq_of_card_eq_two hS hx hy hx1 hy1

theorem isGoldCaseSp42Cat_of_card_omegaOneCenter [Finite D] {H₁ H₂ : Subgroup D}
    (hG : IsGoldschmidtTriple H₁ H₂) (h : IsGoldCaseVICat H₁ H₂) (h₁ : CharTwo H₁)
    (hm : Nat.card ↥(omegaOneCenterOf (H₁ ⊓ H₂)) = 4) : IsGoldCaseSp42 H₁ H₂ := by
  rcases h with h | h | h | h | h | ⟨-, -, -, -, -, -, hZ2, -⟩
  · exact isGoldCaseSp42_of_card_omegaOneCenter hG (Or.inl h) h₁ hm
  · exact h
  · exact isGoldCaseSp42_of_card_omegaOneCenter hG (Or.inr (Or.inr (Or.inl h))) h₁ hm
  · exact isGoldCaseSp42_of_card_omegaOneCenter hG (Or.inr (Or.inr (Or.inr (Or.inl h)))) h₁ hm
  · exact isGoldCaseSp42_of_card_omegaOneCenter hG
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))) h₁ hm
  · exfalso
    have := card_omegaOneCenterOf_le_two (centerOf_inf_le_centerOf_pCoreOf hG h₁)
      (atMostOneInvolution_of_card_eq_two hZ2)
    omega

theorem remark_f6_15_isGoldCaseCat (hlist : GoldschmidtS3ListCat.{u}) {D : Type u} [Group D]
    [Finite D] {X : Type*} [Group X] [Finite X] {G₁ G₂ : Subgroup D}
    (h : IsGoldschmidtTriple G₁ G₂) (e : D ≃* X ⧸ CFSG.pPrimeCore 3 X) :
    IsGoldschmidtAmalgam G₁ G₂ ∧ IsGoldCaseCat G₁ G₂ := by
  have hA : IsGoldschmidtAmalgam G₁ G₂ := ⟨h, (remark_f6_15 e).2⟩
  exact ⟨hA, hlist D G₁ G₂ hA⟩

end F6

end CFSG.Quasithin
