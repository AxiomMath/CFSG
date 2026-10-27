module

public import CFSG.Quasithin.Background.E3AParamLeTwoClosure

public section

namespace CFSG.Quasithin.E3

open CFSG.Quasithin
open scoped Pointwise

variable {W : Type} [CommGroup W] [Finite W]

theorem aParam_le_two_of_E8Gen (hW : ∀ w : W, w ^ 2 = 1) (Y : Subgroup (MulAut W))
    (hE8 : ∀ A : Subgroup ↥Y, (∀ a ∈ A, a ^ 2 = 1) → 8 ≤ Nat.card A →
      Nat.card A = 8 ∧
      (⨆ a ∈ A, ⨆ (_ : a ≠ 1), Subgroup.centralizer ({a} : Set ↥Y)) = ⊤ ∧
      Subgroup.normalClosure (A : Set ↥Y) = ⊤ ∧
      ∀ a ∈ A, a ≠ 1 → 3 ∣ Nat.card (Subgroup.centralizer ({a} : Set ↥Y))) :
    E3.aParam Y ≤ 2 := by
  refine aParam_le_two_of_E8GenClosure hW Y fun A hA h8 => ?_
  obtain ⟨h1, h2, h3, h4⟩ := hE8 A hA h8
  have hAne : A ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at h1
    omega
  obtain ⟨⟨a, haA⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hAne
  have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
  refine ⟨h1, h2, a, haA, ha1', ?_⟩
  rw [h3, top_inf_eq]
  exact h4 a haA ha1'

end CFSG.Quasithin.E3
