module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamLab6Crit
public import CFSG.Quasithin.Background.GoldschmidtAmalgamLab7SysAll

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL CFSG.Quasithin.F6.GoldAmLab6
  CFSG.Quasithin.F6.GoldAmLab7

namespace F6

namespace GoldAmLab9

variable {D : Type*} [Group D] [Finite D] {A B : Subgroup D} {V V₂ : Subgroup D} {z c : D}

theorem not_nm_le_flip (h : TwoSys A B z V c V₂) {b : ℕ}
    (hmin : ∀ x y : CosetGeom (A ⊔ B) A B, CosetGeom.dist x y < b →
      Nm A B V V₂ x ≤ ballStab 1 y)
    {α α' : CosetGeom (A ⊔ B) A B} (hdist : CosetGeom.dist α α' = b)
    (hnot : ¬ Nm A B V V₂ α ≤ ballStab 1 α') : ¬ Nm A B V V₂ α' ≤ ballStab 1 α := by
  have hb2 : 2 ≤ b := by
    by_contra hlt
    push Not at hlt
    rcases (by omega : b = 0 ∨ b = 1) with h0 | h1
    · rw [h0] at hdist
      have : α = α' := (dist_eq_zero_iff (G₁ := A) (G₂ := B) rfl).mp hdist
      subst this
      exact hnot (goodV_all h α).nm_le
    · rw [h1] at hdist
      exact hnot (goodE0_all h (dist_eq_one_iff_adj.mp hdist)).nm_le
  obtain ⟨ε, hα'ε, hdε⟩ : ∃ ε, (graph (A ⊔ B) A B).Adj α' ε ∧ CosetGeom.dist α ε = b - 1 := by
    exact exists_adj_dist_eq (G₁ := A) (G₂ := B) rfl (α := α) (δ := α') (d := b - 1)
      (by rw [hdist]; omega)
  have hle : Nm A B V V₂ α ≤ stab α' := fun a ha =>
    ballStab_le_stab_of_dist_le (n := 1) (γ := ε) (δ := α')
      (dist_eq_one_iff_adj.mpr hα'ε.symm).le (hmin α ε (by omega) ha)
  exact not_nm_le_symm (goodV_all h α) (goodV_all h α') hle hnot

end GoldAmLab9

end F6

end CFSG.Quasithin
