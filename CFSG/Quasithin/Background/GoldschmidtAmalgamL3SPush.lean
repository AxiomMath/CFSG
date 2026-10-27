module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL1Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmL3

variable {D : Type*} [Group D] [Finite D] {A B : Subgroup D}

theorem ballStab_one_γ₀_eq_pCoreOf (h : GoldHyp A B) :
    ballStab 1 (γ₀ (A ⊔ B) A B) = pCoreOf 2 A := by
  have hA : stab (γ₀ (A ⊔ B) A B) = A := stab_γ₀ (le_sup_left : A ≤ A ⊔ B)
  have hB : stab (γ₁ (A ⊔ B) A B) = B := stab_γ₁ (le_sup_right : B ≤ A ⊔ B)
  apply le_antisymm
  · have hle : ballStab 1 (γ₀ (A ⊔ B) A B) ≤ A := (ballStab_le_stab 1 _).trans hA.le
    have hN : A ≤ Subgroup.normalizer (ballStab 1 (γ₀ (A ⊔ B) A B) : Set D) := by
      have := le_normalizer_ballStab (G₀ := A ⊔ B) (G₁ := A) (G₂ := B) 1 (γ₀ (A ⊔ B) A B)
      rwa [hA] at this
    have hB1 : ballStab 1 (γ₀ (A ⊔ B) A B) ≤ stab (γ₁ (A ⊔ B) A B) :=
      ballStab_le_stab_of_dist_le (dist_eq_one_iff_adj.mpr (adj_γ₀_γ₁ (G₀ := A ⊔ B) (G₁ := A)
        (G₂ := B))).le
    exact le_pCoreOf_of_le_normalizer 2 hle hN
      (h.isSylowTwoOf_left.2.1.to_le (le_inf hle (hB1.trans hB.le)))
  · have := pCoreOf_stab_le_ballStab_one h.amalgamHyp (γ₀ (A ⊔ B) A B)
    rwa [hA] at this

theorem ballStab_one_γ₁_eq_pCoreOf (h : GoldHyp A B) :
    ballStab 1 (γ₁ (A ⊔ B) A B) = pCoreOf 2 B := by
  have hA : stab (γ₀ (A ⊔ B) A B) = A := stab_γ₀ (le_sup_left : A ≤ A ⊔ B)
  have hB : stab (γ₁ (A ⊔ B) A B) = B := stab_γ₁ (le_sup_right : B ≤ A ⊔ B)
  apply le_antisymm
  · have hle : ballStab 1 (γ₁ (A ⊔ B) A B) ≤ B := (ballStab_le_stab 1 _).trans hB.le
    have hN : B ≤ Subgroup.normalizer (ballStab 1 (γ₁ (A ⊔ B) A B) : Set D) := by
      have := le_normalizer_ballStab (G₀ := A ⊔ B) (G₁ := A) (G₂ := B) 1 (γ₁ (A ⊔ B) A B)
      rwa [hB] at this
    have hA1 : ballStab 1 (γ₁ (A ⊔ B) A B) ≤ stab (γ₀ (A ⊔ B) A B) :=
      ballStab_le_stab_of_dist_le (dist_eq_one_iff_adj.mpr (adj_γ₀_γ₁ (G₀ := A ⊔ B) (G₁ := A)
        (G₂ := B)).symm).le
    exact le_pCoreOf_of_le_normalizer 2 hle hN
      (h.isSylowTwoOf_right.2.1.to_le (le_inf (hA1.trans hA.le) hle))
  · have := pCoreOf_stab_le_ballStab_one h.amalgamHyp (γ₁ (A ⊔ B) A B)
    rwa [hB] at this

end GoldAmL3

end F6

end CFSG.Quasithin
