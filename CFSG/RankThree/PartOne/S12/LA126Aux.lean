module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.RankThree.PartOne

namespace LA126

variable {p : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]

def fixedSubmodule (Y : Subgroup (V ≃ₗ[ZMod p] V)) : Submodule (ZMod p) V where
  carrier := {x | ∀ y ∈ Y, y x = x}
  add_mem' {a b} ha hb y hy := by rw [map_add, ha y hy, hb y hy]
  zero_mem' y _ := map_zero y
  smul_mem' c x hx y hy := by rw [map_smul, hx y hy]

theorem mem_fixedSubmodule {Y : Subgroup (V ≃ₗ[ZMod p] V)} {x : V} :
    x ∈ fixedSubmodule Y ↔ ∀ y ∈ Y, y x = x :=
  Iff.rfl

theorem fixedSubmodule_invariant {Γ Y : Subgroup (V ≃ₗ[ZMod p] V)}
    (hYnorm : ∀ g ∈ Γ, ∀ y ∈ Y, g * y * g⁻¹ ∈ Y) {g : V ≃ₗ[ZMod p] V} (hg : g ∈ Γ) {x : V}
    (hx : x ∈ fixedSubmodule Y) : g x ∈ fixedSubmodule Y := by
  intro y hy
  have hmem : g⁻¹ * y * g ∈ Y := by simpa using hYnorm g⁻¹ (Γ.inv_mem hg) y hy
  have h : g⁻¹ (y (g x)) = x := hx _ hmem
  have e : g (g⁻¹ (y (g x))) = y (g x) := LinearEquiv.apply_symm_apply g _
  rw [h] at e
  exact e.symm

end LA126

theorem exists_invariant_line_of_fixed {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] [Module.Finite (ZMod p) V] (Γ : Subgroup (V ≃ₗ[ZMod p] V))
    (B : Submodule (ZMod p) V)
    (hdim : Module.finrank (ZMod p) B + 1 = Module.finrank (ZMod p) V)
    (hinv : ∀ g ∈ Γ, ∀ b ∈ B, g b ∈ B)
    (hfaith : ∀ g ∈ Γ, (∀ b ∈ B, g b = b) → g = 1)
    (hirr : ∀ B' ≤ B, (∀ g ∈ Γ, ∀ b ∈ B', g b ∈ B') → B' = ⊥ ∨ B' = B)
    (Y : Subgroup (V ≃ₗ[ZMod p] V)) (hYΓ : Y ≤ Γ)
    (hYnorm : ∀ g ∈ Γ, ∀ y ∈ Y, g * y * g⁻¹ ∈ Y) (hY1 : Y ≠ ⊥) (v : V) (hv : v ∉ B)
    (hfix : ∀ y ∈ Y, y v = v) :
    ∃ ℓ : Submodule (ZMod p) V, Module.finrank (ZMod p) ℓ = 1 ∧ Disjoint ℓ B ∧
      ∀ g ∈ Γ, ∀ x ∈ ℓ, g x ∈ ℓ := by
  have hCinv : ∀ g ∈ Γ, ∀ x ∈ LA126.fixedSubmodule Y, g x ∈ LA126.fixedSubmodule Y :=
    fun g hg x hx => LA126.fixedSubmodule_invariant hYnorm hg hx
  have hCBinv : ∀ g ∈ Γ, ∀ x ∈ LA126.fixedSubmodule Y ⊓ B, g x ∈ LA126.fixedSubmodule Y ⊓ B :=
    fun g hg x hx => ⟨hCinv g hg x hx.1, hinv g hg x hx.2⟩
  have hnotB : ¬ B ≤ LA126.fixedSubmodule Y := by
    intro hBC
    obtain ⟨y, hy1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hY1
    exact hy1 (Subtype.ext (hfaith y (hYΓ y.2) fun b hb => hBC hb y y.2))
  have hbot : LA126.fixedSubmodule Y ⊓ B = ⊥ :=
    (hirr _ inf_le_right hCBinv).resolve_right fun h => hnotB (h.symm.le.trans inf_le_left)
  have hvC : v ∈ LA126.fixedSubmodule Y := hfix
  have hCne : LA126.fixedSubmodule Y ≠ ⊥ := fun h => hv (by
    rw [h, Submodule.mem_bot] at hvC
    rw [hvC]
    exact B.zero_mem)
  have hlow : 1 ≤ Module.finrank (ZMod p) (LA126.fixedSubmodule Y) :=
    Submodule.one_le_finrank_iff.2 hCne
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq (LA126.fixedSubmodule Y) B
  rw [hbot, finrank_bot] at hsum
  have hle : Module.finrank (ZMod p) ↥(LA126.fixedSubmodule Y ⊔ B) ≤ Module.finrank (ZMod p) V :=
    Submodule.finrank_le _
  refine ⟨LA126.fixedSubmodule Y, ?_, disjoint_iff.2 hbot, hCinv⟩
  omega

end CFSG.RankThree.PartOne
