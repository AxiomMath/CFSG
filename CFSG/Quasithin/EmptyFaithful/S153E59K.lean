module

public import CFSG.Quasithin.EmptyFaithful.S153E59I
public import CFSG.Quasithin.EmptyFaithful.S153EInputs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S1417 CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace S153E59

section X

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}
  (cx : Ctx15350 T Mc M V₁ V₂ t) {N₁ N₂ : Subgroup (MulAut ↥(VZ T M))} {g : G} {s : ℕ}
  {y t₁ : G}

theorem y_mem_Y (c : Chain15358 cx N₁ N₂ g s y t₁) : y ∈ Y153 Mc M :=
  ((oTwoUpper_le _ c.hy.1) : y ∈ Y153 Mc M ⊓ Ni153 T Mc M V₁ N₁).1

omit [Finite G] in
theorem mem_X_iff {x : G} :
    x ∈ Xgp153 T M V₁ Mc y ↔ y * x * y⁻¹ ∈ UH153 T M V₁ Mc ∧
      y * (y * x * y⁻¹) * y⁻¹ ∈ Mc := by
  rw [Xgp153, mem_conjSubgroup_iff, Fgp153, Subgroup.mem_inf, mem_conjSubgroup_iff]

theorem X_le_Mc (c : Chain15358 cx N₁ N₂ g s y t₁) : Xgp153 T M V₁ Mc y ≤ Mc := by
  intro x hx
  obtain ⟨hfU, hfH⟩ := mem_X_iff.mp hx
  set f := y * x * y⁻¹ with hf
  rw [← centralizer_Z_eq cx, Subgroup.mem_centralizer_iff]
  intro z hz
  have hfZ : ∀ z ∈ quasithinOmegaOneCenter T, f * z = z * f := fun z hz =>
    Z_central cx (U_le_Mc cx hfU) hz
  have hfZy : ∀ z'' ∈ conjSubgroup (quasithinOmegaOneCenter T) y, f * z'' = z'' * f := by
    intro z'' hz''
    rw [mem_conjSubgroup_iff] at hz''
    have h1 := Z_central cx hfH hz''
    have e : z'' = y⁻¹ * (y * z'' * y⁻¹) * y := by group
    calc f * z'' = y⁻¹ * ((y * f * y⁻¹) * (y * z'' * y⁻¹)) * y := by rw [e]; group
      _ = y⁻¹ * ((y * z'' * y⁻¹) * (y * f * y⁻¹)) * y := by rw [h1]
      _ = z'' * f := by rw [e]; group
  have hw : y * z * y⁻¹ ∈
      quasithinOmegaOneCenter T ⊔ conjSubgroup (quasithinOmegaOneCenter T) y := by
    have h1 : y * z * y⁻¹ ∈ V0gp153 T Mc M V₁ N₁ := mem_conjClosure c.hy.1 hz
    rw [c.h56.V0_eq] at h1
    exact h1
  have hC : quasithinOmegaOneCenter T ⊔ conjSubgroup (quasithinOmegaOneCenter T) y ≤
      Subgroup.centralizer ({f} : Set G) := by
    refine sup_le (fun z hz => ?_) (fun z'' hz'' => ?_)
    · rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff.mp hh]
      exact hfZ z hz
    · rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff.mp hh]
      exact hfZy z'' hz''
  have hwf : f * (y * z * y⁻¹) = (y * z * y⁻¹) * f :=
    Subgroup.mem_centralizer_iff.mp (hC hw) f rfl
  have hx' : x = y⁻¹ * f * y := by rw [hf]; group
  calc z * x = y⁻¹ * ((y * z * y⁻¹) * f) * y := by rw [hx']; group
    _ = y⁻¹ * (f * (y * z * y⁻¹)) * y := by rw [← hwf]
    _ = x * z := by rw [hx']; group

theorem X_le_IYU (c : Chain15358 cx N₁ N₂ g s y t₁) :
    Xgp153 T M V₁ Mc y ≤ IYU T Mc M V₁ := by
  intro x hx
  obtain ⟨hfU, -⟩ := mem_X_iff.mp hx
  have hy : y ∈ IYU T Mc M V₁ := Y_le_IYU (y_mem_Y cx c)
  have hf : y * x * y⁻¹ ∈ IYU T Mc M V₁ := U_le_IYU hfU
  have e : x = y⁻¹ * (y * x * y⁻¹) * y := by group
  rw [e]
  exact (IYU T Mc M V₁).mul_mem ((IYU T Mc M V₁).mul_mem ((IYU T Mc M V₁).inv_mem hy) hf) hy

theorem X_le_T (c : Chain15358 cx N₁ N₂ g s y t₁) : Xgp153 T M V₁ Mc y ≤ T :=
  fun _ hx => IYU_inf_Mc_le_T cx (X_le_IYU cx c hx) (X_le_Mc cx c hx)

end X

end S153E59

end CFSG.Quasithin
