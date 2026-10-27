module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL1Bound

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmL

namespace GoldHyp

variable {D : Type*} [Group D] [Finite D] {A B : Subgroup D}

omit [Finite D] in
theorem eq_one_of_commute_both (h : GoldHyp A B) {ε : D} (hεT : ε ∈ A ⊓ B)
    (h₁ : ∀ g ∈ A, g * ε = ε * g) (h₂ : ∀ g ∈ B, g * ε = ε * g) : ε = 1 := by
  have hnorm : ∀ {X : Subgroup D}, (∀ g ∈ X, g * ε = ε * g) →
      X ≤ Subgroup.normalizer (Subgroup.zpowers ε : Set D) := fun hX g hg => by
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    exact ((show Commute g ε from hX g hg).zpow_right k).symm.eq
  have hN : Subgroup.zpowers ε = ⊥ :=
    h.eq_bot_of_normalizes (hnorm h₁) (hnorm h₂) (Subgroup.zpowers_le.mpr hεT)
  exact Subgroup.mem_bot.mp (hN ▸ Subgroup.mem_zpowers ε)

end GoldHyp

end GoldAmL

end F6

end CFSG.Quasithin
