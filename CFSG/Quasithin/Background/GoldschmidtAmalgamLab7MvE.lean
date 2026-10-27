module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamLab7Fx
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3RLab

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL CFSG.Quasithin.F6.GoldAmLab6

namespace F6

namespace GoldAmLab7

variable {D : Type*} [Group D] [Finite D] {A B : Subgroup D} {V V₂ : Subgroup D} {z c : D}

theorem goodE_base0 (h : TwoSys A B z V c V₂) (hmv : ∃ g ∈ A, g * c * g⁻¹ ≠ c) :
    GoodE V V₂ (γ₀ (A ⊔ B) A B) (γ₁ (A ⊔ B) A B) := by
  have hE := goodE0_γ₀_γ₁ h
  refine ⟨hE.nm_le, hE.index, hE.ne, hE.rel3, c, fun x hx => fx_base1 h hx, fun g hg hc => ?_⟩
  rw [stab_γ₀ le_sup_left] at hg
  rw [stab_γ₁ le_sup_right]
  exact mem_of_centralizes h.gold h.nat₂ hmv hg hc

theorem goodE_of_typ0 (h : TwoSys A B z V c V₂) (hmv : ∃ g ∈ A, g * c * g⁻¹ ≠ c)
    {γ δ : CosetGeom (A ⊔ B) A B} (hγ : vtype γ = false)
    (hadj : (graph (A ⊔ B) A B).Adj γ δ) : GoodE V V₂ γ δ := by
  have hA : A ≤ Subgroup.normalizer (V : Set D) := h.nat.reduced.2.1
  have hB : B ≤ Subgroup.normalizer (V₂ : Set D) := h.nat₂.reduced.2.1
  obtain ⟨g, rfl, rfl⟩ := exists_smul_edge_AB hadj hγ
  exact GoodE.smul hA hB g (goodE_base0 h hmv)

end GoldAmLab7

end F6

end CFSG.Quasithin
