module

public import CFSG.Quasithin.Background.F6GoldschmidtListCat

public section

universe u

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace F6

@[expose] def GoldschmidtNonCharTwoList : Prop :=
  ∀ (D : Type u) [Group D] [Finite D] (G₁ G₂ : Subgroup D), IsGoldschmidtAmalgam G₁ G₂ →
    ¬ (CharTwo G₁ ∧ CharTwo G₂) → IsGoldCaseCat G₁ G₂

@[expose] def GoldschmidtCharTwoSmall : Prop :=
  ∀ (D : Type u) [Group D] [Finite D] (G₁ G₂ : Subgroup D), IsGoldschmidtAmalgam G₁ G₂ →
    CharTwo G₁ → CharTwo G₂ → Nat.card ↥(G₁ ⊓ G₂) ≤ 16 → IsGoldCaseCat G₁ G₂

@[expose] def GoldschmidtCharTwoLarge : Prop :=
  ∀ (D : Type u) [Group D] [Finite D] (G₁ G₂ : Subgroup D), IsGoldschmidtAmalgam G₁ G₂ →
    CharTwo G₁ → CharTwo G₂ → 32 ≤ Nat.card ↥(G₁ ⊓ G₂) → IsGoldCaseCat G₁ G₂

theorem le_sixteen_or_thirtytwo_le_of_pow {n k : ℕ} (h : n = 2 ^ k) : n ≤ 16 ∨ 32 ≤ n := by
  subst h
  rcases Nat.lt_or_ge k 5 with hk | hk
  · left
    calc 2 ^ k ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 16 := by norm_num
  · right
    calc 32 = 2 ^ 5 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk

theorem goldschmidtS3ListCat_of_split (h₁ : GoldschmidtNonCharTwoList.{u})
    (h₂ : GoldschmidtCharTwoSmall.{u}) (h₃ : GoldschmidtCharTwoLarge.{u}) :
    GoldschmidtS3ListCat.{u} := by
  intro D _ _ G₁ G₂ h
  by_cases hc : CharTwo G₁ ∧ CharTwo G₂
  · obtain ⟨k, hk⟩ := (h.toIsGoldschmidtTriple.isPGroup_inf).exists_card_eq
    rcases le_sixteen_or_thirtytwo_le_of_pow hk with h16 | h32
    · exact h₂ D G₁ G₂ h hc.1 hc.2 h16
    · exact h₃ D G₁ G₂ h hc.1 hc.2 h32
  · exact h₁ D G₁ G₂ h hc

end F6

end CFSG.Quasithin
