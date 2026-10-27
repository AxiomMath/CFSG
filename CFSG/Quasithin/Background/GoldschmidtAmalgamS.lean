module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamSplit
public import CFSG.Quasithin.Background.GoldschmidtAmalgamSCaseL32
public import CFSG.Quasithin.Background.GoldschmidtAmalgamSCaseSp42

public section

universe u

namespace CFSG.Quasithin.F6

open CFSG.Open CFSG.QuasithinUnique

theorem goldschmidtCharTwoSmall_holds : GoldschmidtCharTwoSmall.{u} := by
  intro D _ _ G₁ G₂ h c₁ c₂ hT16
  obtain ⟨k, hk⟩ := (h.toIsGoldschmidtTriple.isPGroup_inf).exists_card_eq
  have h8 := GoldAmS.eight_le_card_of_charTwo h.toIsGoldschmidtTriple c₁
  have h2k : Nat.card ↥(G₁ ⊓ G₂) = 8 ∨ Nat.card ↥(G₁ ⊓ G₂) = 16 := by
    rw [hk] at h8 hT16 ⊢
    have hk3 : 3 ≤ k := by
      by_contra hlt
      push Not at hlt
      have : 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hk4 : k ≤ 4 := by
      by_contra hlt
      push Not at hlt
      have : 2 ^ 5 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    interval_cases k <;> simp
  rcases h2k with h8' | h16
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (GoldAmS.goldCaseL32_of_amalgam h c₁ c₂ h8')))))))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (GoldAmS.goldCaseSp42_of_amalgam h c₁ c₂ h16))))))))

end CFSG.Quasithin.F6
