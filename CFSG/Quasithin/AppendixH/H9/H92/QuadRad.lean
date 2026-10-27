module

public import CFSG.Quasithin.AppendixH.H9.H92.QuadRad.EmbeddingIntoHom
public import CFSG.Quasithin.AppendixH.H9.H92.QuadRad.FixedSpace

public section

open scoped Matrix

namespace CFSG.ASVolI.ChH

private theorem two_or_three_of_le_mul {a b : ℕ} (hba : b ≤ a) (ha : a ≤ 5)
    (h : 5 ≤ (5 - a) * b) : b = 2 ∨ b = 3 := by
  have hb : b ≤ 5 := hba.trans ha
  interval_cases a <;> interval_cases b <;> omega

theorem exists_rad_of_quadratic (E : Subgroup (GL (Fin 5) (ZMod 2)))
    (hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hsq : ∀ a ∈ E, a * a = 1)
    (hq : ∀ g ∈ E, ∀ h ∈ E, ((g : Matrix (Fin 5) (Fin 5) (ZMod 2)) - 1) *
      ((h : Matrix (Fin 5) (Fin 5) (ZMod 2)) - 1) = 0)
    (h32 : 32 ≤ Nat.card E) :
    ∃ D : Submodule (ZMod 2) (Fin 5 → ZMod 2),
      (Module.finrank (ZMod 2) D = 2 ∨ Module.finrank (ZMod 2) D = 3) ∧
        ∀ g ∈ E, (∀ x : Fin 5 → ZMod 2, ((g : Matrix (Fin 5) (Fin 5) (ZMod 2)) - 1) *ᵥ x ∈ D) ∧
          ∀ u ∈ D, (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ u = u := by
  have hDF : matMoveSpace 5 E ≤ matFixSpace 5 E := matMoveSpace_le_matFixSpace hq
  have hba : Module.finrank (ZMod 2) (matMoveSpace 5 E) ≤
      Module.finrank (ZMod 2) (matFixSpace 5 E) := Submodule.finrank_mono hDF
  have ha5 : Module.finrank (ZMod 2) (matFixSpace 5 E) ≤ 5 := by
    have h := Submodule.finrank_le (matFixSpace 5 E)
    rwa [Module.finrank_fin_fun] at h
  have hpow : 2 ^ 5 ≤ 2 ^ ((5 - Module.finrank (ZMod 2) (matFixSpace 5 E)) *
      Module.finrank (ZMod 2) (matMoveSpace 5 E)) :=
    calc 2 ^ 5 = 32 := by norm_num
      _ ≤ Nat.card E := h32
      _ ≤ _ := natCard_le_two_pow_finrank_fix_move 5 E
  have h5 : 5 ≤ (5 - Module.finrank (ZMod 2) (matFixSpace 5 E)) *
      Module.finrank (ZMod 2) (matMoveSpace 5 E) :=
    (Nat.pow_le_pow_iff_right (by norm_num)).mp hpow
  refine ⟨matMoveSpace 5 E, two_or_three_of_le_mul hba ha5 h5, fun g hg => ⟨fun x => ?_, fun u hu => ?_⟩⟩
  · exact sub_one_mulVec_mem_matMoveSpace hg x
  · exact mem_matFixSpace.mp (hDF hu) g hg

end CFSG.ASVolI.ChH
