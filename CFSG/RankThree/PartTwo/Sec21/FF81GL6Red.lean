module

public import CFSG.RankThree.PartTwo.Sec21.FF81GL6Defs
public import CFSG.RankThree.PartTwo.Sec21.FF81Sec57Defs

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.GL6

open Matrix

abbrev cj (g : G6) : G6 →* G6 := (MulAut.conj g).toMonoidHom

theorem cj_apply (g x : G6) : cj g x = g * x * g⁻¹ := rfl

theorem map_centralizer_cj (g u : G6) :
    (Subgroup.centralizer {u}).map (cj g) = Subgroup.centralizer {g * u * g⁻¹} := by
  ext x
  simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff, cj_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    calc g * y * g⁻¹ * (g * u * g⁻¹) = g * (y * u) * g⁻¹ := by group
      _ = g * (u * y) * g⁻¹ := by rw [hy]
      _ = g * u * g⁻¹ * (g * y * g⁻¹) := by group
  · intro hx
    refine ⟨g⁻¹ * x * g, ?_, by group⟩
    calc g⁻¹ * x * g * u = g⁻¹ * (x * (g * u * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * u * g⁻¹) * x) * g := by rw [hx]
      _ = u * (g⁻¹ * x * g) := by group

theorem map_zpowers_cj (g u : G6) :
    (Subgroup.zpowers u).map (cj g) = Subgroup.zpowers (g * u * g⁻¹) := by
  rw [MonoidHom.map_zpowers, cj_apply]

theorem card_map_cj (g : G6) (H : Subgroup G6) : Nat.card (H.map (cj g)) = Nat.card H :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem kf_sp6GL6Cen_of
    (hU0 : ∀ {u : G6}, orderOf u = 3 →
      16 ≤ Nat.card {v : Fin 6 → ZMod 2 // (u : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ v = v} →
      ∃ g : G6, g * u * g⁻¹ = u0)
    (hSig : ∀ φ : Equiv.Perm (Fin 6) →* G6, φ (Equiv.swap 0 1 * Equiv.swap 1 2) ≠ 1 →
      φ.range ≤ Subgroup.centralizer {u0} →
      ∃ g ∈ Subgroup.centralizer {u0}, φ.range.map (cj g) = Sig0)
    (hEq : ∀ X : Subgroup G6, X ⊓ Subgroup.centralizer {u0} = K0 → 81 ∣ Nat.card X → X = Sp0)
    (hcard : Nat.card Sp0 = 1451520)
    (hgen : Sp0 = Subgroup.closure
      {g | g ∈ Sp0 ∧ ((g : Matrix (Fin 6) (Fin 6) (ZMod 2)) - 1).rank = 1})
    (hirr : ∀ W : Submodule (ZMod 2) (Fin 6 → ZMod 2),
      (∀ g ∈ Sp0, ∀ w ∈ W, (g : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ w ∈ W) → W = ⊥ ∨ W = ⊤) :
    KF_Sp6GL6Cen := by
  intro X u φ h3 h16 hφ hX h81
  obtain ⟨g₁, hg₁⟩ := hU0 h3 h16
  set φ₁ : Equiv.Perm (Fin 6) →* G6 := (cj g₁).comp φ with hφ₁def
  have hφ₁ : φ₁ (Equiv.swap 0 1 * Equiv.swap 1 2) ≠ 1 := by
    intro h
    apply hφ
    have h' : g₁ * φ (Equiv.swap 0 1 * Equiv.swap 1 2) * g₁⁻¹ = 1 := h
    calc φ (Equiv.swap 0 1 * Equiv.swap 1 2)
        = g₁⁻¹ * (g₁ * φ (Equiv.swap 0 1 * Equiv.swap 1 2) * g₁⁻¹) * g₁ := by group
      _ = 1 := by rw [h']; group
  have hrange : φ₁.range = φ.range.map (cj g₁) := by
    rw [hφ₁def, MonoidHom.range_comp]
  have hφC : φ.range ≤ Subgroup.centralizer {u} := by
    have : φ.range ≤ X ⊓ Subgroup.centralizer {u} := hX ▸ le_sup_left
    exact this.trans inf_le_right
  have hC₁ : φ₁.range ≤ Subgroup.centralizer {u0} := by
    rw [hrange, ← hg₁, ← map_centralizer_cj]
    exact Subgroup.map_mono hφC
  obtain ⟨g₂, hg₂C, hg₂⟩ := hSig φ₁ hφ₁ hC₁
  set g := g₂ * g₁ with hgdef
  have hg₂u : g₂ * u0 * g₂⁻¹ = u0 := by
    rw [Subgroup.mem_centralizer_singleton_iff] at hg₂C
    rw [hg₂C]; group
  have hgu : g * u * g⁻¹ = u0 := by
    calc g * u * g⁻¹ = g₂ * (g₁ * u * g₁⁻¹) * g₂⁻¹ := by rw [hgdef]; group
      _ = u0 := by rw [hg₁, hg₂u]
  have hcj : cj g = (cj g₂).comp (cj g₁) := by
    ext x; simp only [cj_apply, MonoidHom.comp_apply, hgdef]; group
  have hmapφ : φ.range.map (cj g) = Sig0 := by
    rw [hcj, ← Subgroup.map_map, ← hrange, hg₂]
  set X' := X.map (cj g) with hX'def
  have hX' : X' ⊓ Subgroup.centralizer {u0} = K0 := by
    rw [← hgu, ← map_centralizer_cj, hX'def,
      ← Subgroup.map_inf_eq X _ (cj g) (MulAut.conj g).injective, hX, Subgroup.map_sup,
      hmapφ, map_zpowers_cj, hgu]
    rfl
  have h81' : 81 ∣ Nat.card X' := by rw [hX'def, card_map_cj]; exact h81
  have hX'eq : X' = Sp0 := hEq X' hX' h81'
  have hXeq : X = Sp0.map (cj g⁻¹) := by
    rw [← hX'eq, hX'def, Subgroup.map_map]
    conv_lhs => rw [← Subgroup.map_id X]
    congr 1
    ext x; simp only [cj_apply, MonoidHom.comp_apply, MonoidHom.id_apply]; group
  have hmemX : ∀ s ∈ Sp0, g⁻¹ * s * g ∈ X := by
    intro s hs
    rw [hXeq]
    exact ⟨s, hs, by rw [cj_apply, inv_inv]⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [hXeq, card_map_cj, hcard]
  · have hrk : ∀ s : G6, ((g⁻¹ * s * g : G6) : Matrix (Fin 6) (Fin 6) (ZMod 2)) - 1 =
        (g⁻¹ : G6).val * ((s : Matrix (Fin 6) (Fin 6) (ZMod 2)) - 1) * g.val := by
      intro s
      have h1 : (g⁻¹ : G6).val * g.val = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
      simp only [Units.val_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, h1]
    have hrank : ∀ s : G6, (((g⁻¹ * s * g : G6) : Matrix (Fin 6) (Fin 6) (ZMod 2)) - 1).rank =
        ((s : Matrix (Fin 6) (Fin 6) (ZMod 2)) - 1).rank := by
      intro s
      rw [hrk, Matrix.rank_mul_eq_left_of_isUnit_det _ _ (Matrix.isUnits_det_units g),
        Matrix.rank_mul_eq_right_of_isUnit_det _ _ (Matrix.isUnits_det_units g⁻¹)]
    conv_lhs => rw [hXeq, hgen, MonoidHom.map_closure]
    congr 1
    ext h
    simp only [Set.mem_image, Set.mem_setOf_eq, cj_apply, inv_inv]
    constructor
    · rintro ⟨s, ⟨hs, hs1⟩, rfl⟩
      exact ⟨hmemX s hs, by rw [hrank]; exact hs1⟩
    · rintro ⟨hX, h1⟩
      rw [hXeq] at hX
      obtain ⟨s, hs, rfl⟩ := hX
      rw [cj_apply, inv_inv] at h1 ⊢
      exact ⟨s, ⟨hs, by rw [← hrank]; exact h1⟩, rfl⟩
  · intro W hW
    set W'' : Submodule (ZMod 2) (Fin 6 → ZMod 2) :=
      W.comap (Matrix.toLin' ((g⁻¹ : G6) : Matrix (Fin 6) (Fin 6) (ZMod 2))) with hW''
    have hinv : ∀ v : Fin 6 → ZMod 2,
        ((g⁻¹ : G6) : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ ((g : Matrix _ _ _) *ᵥ v) = v := by
      intro v
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    have hinv' : ∀ v : Fin 6 → ZMod 2,
        (g : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ (((g⁻¹ : G6) : Matrix _ _ _) *ᵥ v) = v := by
      intro v
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    have hW''inv : ∀ s ∈ Sp0, ∀ w ∈ W'', (s : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ w ∈ W'' := by
      intro s hs w hw
      simp only [hW'', Submodule.mem_comap, Matrix.toLin'_apply] at hw ⊢
      have := hW _ (hmemX s hs) _ hw
      have heq : ((g⁻¹ * s * g : G6) : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ
          (((g⁻¹ : G6) : Matrix _ _ _) *ᵥ w) =
          ((g⁻¹ : G6) : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ ((s : Matrix _ _ _) *ᵥ w) := by
        rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hinv']
      rwa [heq] at this
    rcases hirr W'' hW''inv with h | h
    · left
      rw [eq_bot_iff]
      intro w hw
      have : (g : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ w ∈ W'' := by
        simp only [hW'', Submodule.mem_comap, Matrix.toLin'_apply, hinv]; exact hw
      rw [h, Submodule.mem_bot] at this
      rw [Submodule.mem_bot, ← hinv w, this, Matrix.mulVec_zero]
    · right
      rw [eq_top_iff]
      intro w _
      have : (g : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ w ∈ W'' := by rw [h]; trivial
      simpa only [hW'', Submodule.mem_comap, Matrix.toLin'_apply, hinv] using this

end CFSG.RankThree.PartTwo.Sec21.FF81.GL6
