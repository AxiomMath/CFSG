module

public import CFSG.RankThree.GF2n.Smith81.S81VOrth

public section

namespace CFSG.RankThree.GF2n.Smith81.S81V

open CFSG.ClassicalGroups.Unitary CFSG.RankThree.GF2n.Smith81.U6Cube Module

variable {F : Type} [Field F] {σ : F ≃+* F}

private theorem lemmaB_inf_span_eq_bot {Y : Submodule F (Fin 6 → F)} {w : Fin 6 → F}
    (hw : w ∉ Y) : Y ⊓ Submodule.span F {w} = ⊥ := by
  rw [eq_bot_iff]
  rintro v ⟨hvY, hvw⟩
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hvw
  by_cases ha : a = 0
  · simp [ha]
  · exfalso
    apply hw
    have h := Y.smul_mem a⁻¹ hvY
    rwa [smul_smul, inv_mul_cancel₀ ha, one_smul] at h

private theorem lemmaB_isTotIso_span {x : Fin 6 → F} (hx : herm σ x x = 0) :
    IsTotIso σ (Submodule.span F {x}) := by
  intro a ha b hb
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp ha
  obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.mp hb
  simp [hx]

private theorem lemmaB_isTotIso_sup {W₁ W₂ : Submodule F (Fin 6 → F)}
    (hσ : ∀ c, σ (σ c) = c) (h₁ : IsTotIso σ W₁) (h₂ : IsTotIso σ W₂)
    (h₁₂ : ∀ u ∈ W₁, ∀ v ∈ W₂, herm σ u v = 0) : IsTotIso σ (W₁ ⊔ W₂) := by
  intro a ha b hb
  obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp ha
  obtain ⟨u', hu', v', hv', rfl⟩ := Submodule.mem_sup.mp hb
  simp only [herm_add_left, herm_add_right, h₁ u hu u' hu', h₁₂ u hu v' hv',
    herm_eq_zero_comm σ hσ (h₁₂ u' hu' v hv), h₂ v hv v' hv', add_zero]

private theorem lemmaB_finrank_inf_orth {G : Submodule F (Fin 6 → F)}
    (hσ : ∀ c, σ (σ c) = c) (hG3 : finrank F G = 3) {x z : Fin 6 → F} (hx0 : x ≠ 0)
    (hzG : z ∈ G) (hxz : herm σ x z ≠ 0) :
    finrank F ↥(G ⊓ orth σ (Submodule.span F {x})) = 2 := by
  have hO : finrank F ↥(orth σ (Submodule.span F {x})) = 5 := by
    have h := finrank_orth hσ (Submodule.span F {x})
    rw [finrank_span_singleton hx0] at h
    omega
  have hzO : z ∉ orth σ (Submodule.span F {x}) := by
    intro h
    exact hxz ((mem_orth (σ := σ)).mp h x (Submodule.mem_span_singleton_self x))
  have hlt : orth σ (Submodule.span F {x}) < G ⊔ orth σ (Submodule.span F {x}) := by
    refine lt_of_le_of_ne le_sup_right ?_
    intro h
    apply hzO
    rw [h]
    exact Submodule.mem_sup_left hzG
  have hsup : finrank F ↥(G ⊔ orth σ (Submodule.span F {x})) = 6 := by
    have h1 := Submodule.finrank_lt_finrank_of_lt hlt
    have h2 := Submodule.finrank_le (G ⊔ orth σ (Submodule.span F {x}))
    rw [Module.finrank_fin_fun] at h2
    omega
  have h := Submodule.finrank_sup_add_finrank_inf_eq G (orth σ (Submodule.span F {x}))
  omega

theorem lemmaB (hσ : ∀ c, σ (σ c) = c) {X : Set (Submodule F (Fin 6 → F))}
    {R : Submodule F (Fin 6 → F)} {x y z : Fin 6 → F}
    (hx : herm σ x x = 0) (hy : herm σ y y = 0) (hxy : herm σ x y ≠ 0)
    (hxR : ∀ r ∈ R, herm σ r x = 0) (hyR : ∀ r ∈ R, herm σ r y = 0)
    (hz : z ∈ Submodule.span F {x, y}) (hz0 : z ≠ 0) (hzz : herm σ z z = 0)
    (hGx : ∀ G, IsPt σ G → R ≤ G → x ∈ G → GenPts σ X G)
    (hGy : ∀ G, IsPt σ G → R ≤ G → y ∈ G → GenPts σ X G) :
    ∀ G, IsPt σ G → R ≤ G → z ∈ G → GenPts σ X G := by
  intro G hG hRG hzG
  obtain ⟨hGti, hG3⟩ := hG
  obtain ⟨α, β, hab⟩ := Submodule.mem_span_pair.mp hz
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hxy (by simp)
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact hxy (by simp)
  have hxz_eq : herm σ x z = β * herm σ x y := by
    rw [← hab, herm_add_right, herm_smul_right, herm_smul_right, hx, mul_zero, zero_add]
  by_cases hxz : herm σ x z = 0
  ·
    have hβ : β = 0 := by
      rw [hxz_eq] at hxz
      exact (mul_eq_zero.mp hxz).resolve_right hxy
    have hα : α ≠ 0 := by
      rintro rfl
      apply hz0
      rw [← hab]
      simp [hβ]
    have hxG : x ∈ G := by
      have h := Submodule.smul_mem G α⁻¹ hzG
      rw [← hab, hβ, zero_smul, add_zero, smul_smul, inv_mul_cancel₀ hα, one_smul] at h
      exact h
    exact hGx G ⟨hGti, hG3⟩ hRG hxG
  ·
    have hβ : β ≠ 0 := by
      rintro rfl
      apply hxz
      rw [hxz_eq, zero_mul]
    obtain ⟨Y, hYdef⟩ : ∃ Y : Submodule F (Fin 6 → F),
        Y = G ⊓ orth σ (Submodule.span F {x}) := ⟨_, rfl⟩
    have hYmem : ∀ u, u ∈ Y ↔ u ∈ G ∧ u ∈ orth σ (Submodule.span F {x}) := by
      intro u
      rw [hYdef, Submodule.mem_inf]
    have hYG : ∀ u ∈ Y, u ∈ G := fun u hu => ((hYmem u).mp hu).1
    have hYfin : finrank F ↥Y = 2 := by
      rw [hYdef]
      exact lemmaB_finrank_inf_orth hσ hG3 hx0 hzG hxz
    have hYx : ∀ u ∈ Y, herm σ x u = 0 := fun u hu =>
      (mem_orth (σ := σ)).mp ((hYmem u).mp hu).2 x (Submodule.mem_span_singleton_self x)
    have hYxr : ∀ u ∈ Y, herm σ u x = 0 := fun u hu => herm_eq_zero_comm σ hσ (hYx u hu)
    have hYti : IsTotIso σ Y := by
      intro u hu v hv
      exact hGti u (hYG u hu) v (hYG v hv)
    have hYy : ∀ u ∈ Y, herm σ u y = 0 := by
      intro u hu
      have h1 : herm σ u z = 0 := hGti u (hYG u hu) z hzG
      rw [← hab] at h1
      simp only [herm_add_right, herm_smul_right] at h1
      rw [hYxr u hu, mul_zero, zero_add] at h1
      exact (mul_eq_zero.mp h1).resolve_left hβ
    have hxY : x ∉ Y := fun h => hxz (hGti x (hYG x h) z hzG)
    have hyY : y ∉ Y := fun h => hxy (hYx y h)
    have hRY : R ≤ Y := by
      intro r hr
      rw [hYmem]
      refine ⟨hRG hr, ?_⟩
      rw [mem_orth]
      intro w hw
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hw
      rw [herm_smul_left, herm_eq_zero_comm σ hσ (hxR r hr), mul_zero]
    obtain ⟨Gx, hGxdef⟩ : ∃ W : Submodule F (Fin 6 → F), W = Y ⊔ Submodule.span F {x} :=
      ⟨_, rfl⟩
    obtain ⟨Gy, hGydef⟩ : ∃ W : Submodule F (Fin 6 → F), W = Y ⊔ Submodule.span F {y} :=
      ⟨_, rfl⟩
    have hGxLin : ∀ v ∈ Gx, herm σ x v = 0 := by
      intro v hv
      rw [hGxdef, Submodule.mem_sup] at hv
      obtain ⟨u, hu, w, hw, rfl⟩ := hv
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hw
      simp [herm_add_right, herm_smul_right, hYx u hu, hx]
    have hGyYof : ∀ v ∈ Gy, herm σ x v = 0 → v ∈ Y := by
      intro v hv hxv
      rw [hGydef, Submodule.mem_sup] at hv
      obtain ⟨u, hu, w, hw, rfl⟩ := hv
      obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hw
      rw [herm_add_right, herm_smul_right, hYx u hu, zero_add] at hxv
      have hb : b = 0 := (mul_eq_zero.mp hxv).resolve_right hxy
      rw [hb, zero_smul, add_zero]
      exact hu
    have hGxGy : Gx ⊓ Gy = Y := by
      apply le_antisymm
      · intro v hv
        exact hGyYof v (Submodule.mem_inf.mp hv).2 (hGxLin v (Submodule.mem_inf.mp hv).1)
      · intro v hv
        refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
        · rw [hGxdef]
          exact Submodule.mem_sup_left hv
        · rw [hGydef]
          exact Submodule.mem_sup_left hv
    have hYGx : Y ≤ Gx := by
      rw [hGxdef]
      exact le_sup_left
    have hYGy : Y ≤ Gy := by
      rw [hGydef]
      exact le_sup_left
    have hxGx : x ∈ Gx := by
      rw [hGxdef]
      exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self x)
    have hyGy : y ∈ Gy := by
      rw [hGydef]
      exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self y)
    have hGxti : IsTotIso σ Gx := by
      rw [hGxdef]
      refine lemmaB_isTotIso_sup hσ hYti (lemmaB_isTotIso_span hx) ?_
      intro u hu v hv
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hv
      rw [herm_smul_right, hYxr u hu, mul_zero]
    have hGyti : IsTotIso σ Gy := by
      rw [hGydef]
      refine lemmaB_isTotIso_sup hσ hYti (lemmaB_isTotIso_span hy) ?_
      intro u hu v hv
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hv
      rw [herm_smul_right, hYy u hu, mul_zero]
    have hfinGx : finrank F ↥Gx = 3 := by
      have h := Submodule.finrank_sup_add_finrank_inf_eq Y (Submodule.span F {x})
      rw [lemmaB_inf_span_eq_bot hxY, finrank_bot, finrank_span_singleton hx0, hYfin,
        ← hGxdef] at h
      omega
    have hfinGy : finrank F ↥Gy = 3 := by
      have h := Submodule.finrank_sup_add_finrank_inf_eq Y (Submodule.span F {y})
      rw [lemmaB_inf_span_eq_bot hyY, finrank_bot, finrank_span_singleton hy0, hYfin,
        ← hGydef] at h
      omega
    have hGxne : Gx ≠ Gy := by
      intro hGG
      have h1 : Gx ⊓ Gy = Gx := by rw [hGG, inf_idem]
      rw [hGxGy] at h1
      have h2 : finrank F ↥Y = finrank F ↥Gx := by rw [h1]
      omega
    have hfin : finrank F ↥(Gx ⊓ Gy) = 2 := by
      rw [hGxGy]
      exact hYfin
    have hle : Gx ⊓ Gy ≤ G := by
      rw [hGxGy]
      intro u hu
      exact hYG u hu
    have hX1 : GenPts σ X Gx := hGx Gx ⟨hGxti, hfinGx⟩ (hRY.trans hYGx) hxGx
    have hX2 : GenPts σ X Gy := hGy Gy ⟨hGyti, hfinGy⟩ (hRY.trans hYGy) hyGy
    exact GenPts.line hX1 hX2 hGxne ⟨hGxti, hfinGx⟩ ⟨hGyti, hfinGy⟩ ⟨hGti, hG3⟩ hfin hle

end CFSG.RankThree.GF2n.Smith81.S81V
