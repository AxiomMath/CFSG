module

public import CFSG.GroupTheory.LocalCores.Layer
public import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.GroupTheory.Fitting.LayerTopBot
public import CFSG.Quasithin.Background.A3ComponentsBasic

public section

namespace CFSG.Quasithin.H13.Ch4.G443J4.Lay

open CFSG.Open CFSG.Quasithin

variable {Y : Type} [Group Y] [Finite Y]

omit [Finite Y] in
theorem layer_coe_layer_eq_top (Y : Type) [Group Y] : CFSG.layer ↥(CFSG.layer Y) = ⊤ :=
  CFSG.WholeGroup.layer_layer_eq_top

omit [Finite Y] in
theorem center_layer_eq_bot (hY : CFSG.solvableRadical Y = ⊥) :
    (Subgroup.center (CFSG.layer Y)).map (CFSG.layer Y).subtype = ⊥ :=
  CFSG.WholeGroup.center_layer_eq_bot_of_solvableRadical_eq_bot hY

theorem center_component_eq_bot (hY : CFSG.solvableRadical Y = ⊥) {S : Subgroup Y}
    (hS : CFSG.IsComponent S) : Subgroup.center ↥S = ⊥ := by
  have h1 := CFSG.LocalCores.center_component_le_center_layer hS
  rw [center_layer_eq_bot hY, le_bot_iff] at h1
  exact (Subgroup.map_eq_bot_iff_of_injective _ S.subtype_injective).mp h1

theorem inf_eq_bot_of_ne (hY : CFSG.solvableRadical Y = ⊥) {S T : Subgroup Y}
    (hS : CFSG.IsComponent S) (hT : CFSG.IsComponent T) (hne : S ≠ T) : S ⊓ T = ⊥ := by
  rcases CFSG.LocalCores.distinct_components_commute hS hT with h | h
  · exact absurd h hne
  rw [eq_bot_iff]
  intro x hx
  have hST := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
  have hxc : (⟨x, hx.1⟩ : ↥S) ∈ Subgroup.center ↥S := by
    rw [Subgroup.mem_center_iff]
    intro s
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp (hST s.2) x hx.2).symm
  rw [center_component_eq_bot hY hS, Subgroup.mem_bot] at hxc
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val hxc)

theorem false_of_two_nine (hY : CFSG.solvableRadical Y = ⊥)
    (hrk : CFSG.Open.pRank 3 (CFSG.layer Y) ≤ 2) {S T : Subgroup Y}
    (hS : CFSG.IsComponent S) (hT : CFSG.IsComponent T) (hne : S ≠ T) {A₀ B₀ : Type}
    [Group A₀] [Group B₀] (hAc : ∀ a b : A₀, a * b = b * a) (hA3 : ∀ a : A₀, a ^ 3 = 1)
    (hcA : Nat.card A₀ = 9) (hBc : ∀ a b : B₀, a * b = b * a) (hB3 : ∀ b : B₀, b ^ 3 = 1)
    (hcB : Nat.card B₀ = 9) (f : A₀ →* Y) (hf : Function.Injective f) (hfS : f.range ≤ S)
    (g : B₀ →* Y) (hg : Function.Injective g) (hgT : g.range ≤ T) : False := by
  have hST := Subgroup.commutator_eq_bot_iff_le_centralizer.mp
    ((CFSG.LocalCores.distinct_components_commute hS hT).resolve_left hne)
  have hcomm : ∀ (a : A₀) (b : B₀), Commute (f a) (g b) := fun a b =>
    (Subgroup.mem_centralizer_iff.mp (hST (hfS ⟨a, rfl⟩)) (g b) (hgT ⟨b, rfl⟩)).symm
  set F := f.noncommCoprod g hcomm with hF
  have hinj : Function.Injective F := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    simp only [hF, MonoidHom.noncommCoprod_apply] at h
    have h1 : (f a')⁻¹ * f a = g b' * (g b)⁻¹ := by
      calc (f a')⁻¹ * f a = (f a')⁻¹ * (f a * g b) * (g b)⁻¹ := by group
        _ = (f a')⁻¹ * (f a' * g b') * (g b)⁻¹ := by rw [h]
        _ = g b' * (g b)⁻¹ := by group
    have hm : (f a')⁻¹ * f a ∈ S ⊓ T := ⟨hfS ⟨a'⁻¹ * a, by simp⟩,
      h1 ▸ hgT ⟨b' * b⁻¹, by simp⟩⟩
    rw [inf_eq_bot_of_ne hY hS hT hne, Subgroup.mem_bot] at hm
    have h2 : g b' * (g b)⁻¹ = 1 := h1 ▸ hm
    rw [hf (inv_mul_eq_one.mp hm).symm, hg (mul_inv_eq_one.mp h2).symm]
  have h4 := CFSG.SectionRank.le_pRank_of_injective (p := 3) (by norm_num) (A := A₀ × B₀) (k := 4)
    (fun x y => Prod.ext (hAc x.1 y.1) (hBc x.2 y.2))
    (fun x => Prod.ext (hA3 x.1) (hB3 x.2))
    (by rw [Nat.card_prod, hcA, hcB]; norm_num) F hinj (H := CFSG.layer Y) (by
      rintro _ ⟨⟨a, b⟩, rfl⟩
      exact (CFSG.layer Y).mul_mem (CFSG.LocalCores.component_le_layer hS (hfS ⟨a, rfl⟩))
        (CFSG.LocalCores.component_le_layer hT (hgT ⟨b, rfl⟩)))
  omega

theorem layer_eq_sup_others {S : Subgroup Y} (hS : CFSG.IsComponent S) :
    sSup {T : Subgroup Y | CFSG.IsComponent T ∧ T ≠ S} ≤ Subgroup.centralizer (S : Set Y) ∧
      CFSG.layer Y = S ⊔ sSup {T : Subgroup Y | CFSG.IsComponent T ∧ T ≠ S} :=
  CFSG.WholeGroup.layer_eq_sup_others hS

end CFSG.Quasithin.H13.Ch4.G443J4.Lay
