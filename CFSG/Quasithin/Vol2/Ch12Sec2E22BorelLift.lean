module

public import CFSG.Quasithin.Background.A4Defs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace E2

variable {Γ : Type} [Group Γ]

@[expose] def E22BorelLift (H T MH : Subgroup Γ) (n : ℕ) : Prop :=
  Group.IsSolvable ↥MH ∧
  ∃ R : Subgroup Γ, R ≤ T ∧ IsPGroup 2 ↥R ∧ MH ≤ Subgroup.normalizer (R : Set Γ) ∧
    (∃ C : Subgroup Γ, C ≤ MH ∧ Odd (Nat.card C) ∧ ∃ k : ℕ, C.relIndex MH = 2 ^ k) ∧
    ∀ C : Subgroup Γ, C ≤ MH → Odd (Nat.card C) → (∃ k : ℕ, C.relIndex MH = 2 ^ k) →
      MH ≤ Subgroup.normalizer ((C ⊔ R : Subgroup Γ) : Set Γ) ∧
      MH ⊓ oTwoUpper H ≤ C ⊔ R ∧ IsMulCommutative ↥C ∧
      ∃ Y : Subgroup Γ, Y ≤ C ∧ IsCyclic ↥Y ∧ Nat.card Y = 2 ^ n - 1 ∧
        ∀ A : Subgroup Γ, A ≤ Y → A ≠ ⊥ → ¬ H ⊓ Subgroup.normalizer (A : Set Γ) ≤ MH

end E2

end CFSG.Quasithin
