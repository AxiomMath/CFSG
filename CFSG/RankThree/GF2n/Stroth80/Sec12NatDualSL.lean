module

public import CFSG.RankThree.GF2n.Stroth80.Sec5NatScalars
public import CFSG.ClassicalGroups.SpecialLinear.NaturalNotDual
public import CFSG.ClassicalGroups.SpecialLinear.Transitive

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.Open CFSG.Open.StatedAPI Matrix

variable {F : Type} [Field F] {n : ℕ}

@[expose] def tinvGL (g : GL (Fin n) F) : GL (Fin n) F :=
  ⟨((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)ᵀ, (g : Matrix (Fin n) (Fin n) F)ᵀ,
    by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]⟩

theorem coe_tinvGL (g : GL (Fin n) F) :
    ((tinvGL g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)ᵀ := rfl

theorem coe_tinvGL_inv (g : GL (Fin n) F) :
    (((tinvGL g)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      (g : Matrix (Fin n) (Fin n) F)ᵀ := rfl

theorem tinvGL_one : tinvGL (1 : GL (Fin n) F) = 1 :=
  Units.ext (by simp [coe_tinvGL])

theorem tinvGL_mul (g h : GL (Fin n) F) : tinvGL (g * h) = tinvGL g * tinvGL h :=
  Units.ext (by
    rw [coe_tinvGL, _root_.mul_inv_rev, Units.val_mul, Matrix.transpose_mul, Units.val_mul,
      coe_tinvGL, coe_tinvGL])

theorem tinvGL_tinvGL (g : GL (Fin n) F) : tinvGL (tinvGL g) = g :=
  Units.ext (by rw [coe_tinvGL, coe_tinvGL_inv, Matrix.transpose_transpose])

theorem tinvGL_mem_statedSL {g : GL (Fin n) F} (hg : g ∈ StatedSL n F) :
    tinvGL g ∈ StatedSL n F := by
  rw [mem_statedSL_iff] at hg ⊢
  have h : ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det = 1 := by
    have h1 := det_of_mem_statedSL (inv_mem (mem_statedSL_of_det hg))
    exact h1
  rw [coe_tinvGL, Matrix.det_transpose]
  exact h

open CFSG.Open CFSG.Open.StatedAPI Matrix CFSG.ClassicalGroups.SpecialLinear

theorem eq_zero_of_natDual_equivariant (hn : 3 ≤ n) (f : (Fin n → F) →+ (Fin n → F))
    (hf : ∀ g ∈ StatedSL n F, ∀ x : Fin n → F,
      f ((g : Matrix (Fin n) (Fin n) F) *ᵥ x) =
        ((tinvGL g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ f x) : f = 0 := by
  by_cases h : ∃ v : Fin n → F, v ≠ 0 ∧ f v = 0
  · obtain ⟨v, hv0, hfv⟩ := h
    refine AddMonoidHom.ext fun y => ?_
    rw [AddMonoidHom.zero_apply]
    by_cases hy : y = 0
    · rw [hy, map_zero]
    · obtain ⟨g, hg, hgy⟩ := exists_statedSL_mulVec_eq (by omega : 2 ≤ n) hv0 hy
      have H := hf g hg v
      rw [hfv, Matrix.mulVec_zero, hgy] at H
      exact H
  · have hne : ∀ v : Fin n → F, v ≠ 0 → f v ≠ 0 := fun v hv0 hfv => h ⟨v, hv0, hfv⟩
    have hinj : Function.Injective f := by
      refine (injective_iff_map_eq_zero f).mpr fun a ha => ?_
      by_contra ha0
      exact hne a ha0 ha
    exfalso
    have hdual : ∀ g : GL (Fin n) F, g ∈ StatedSL n F → ∀ x : Fin n → F,
        f ((g : Matrix (Fin n) (Fin n) F) *ᵥ x) =
          ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)ᵀ *ᵥ f x := by
      intro g hg x
      have H := hf g hg x
      rw [coe_tinvGL] at H
      exact H
    exact not_exists_natural_dual_hom_statedSL (K := F) hn ⟨f, hinj, hdual⟩

theorem eq_zero_of_dualNat_equivariant (hn : 3 ≤ n) (f : (Fin n → F) →+ (Fin n → F))
    (hf : ∀ g ∈ StatedSL n F, ∀ y : Fin n → F,
      f (((tinvGL g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ y) =
        (g : Matrix (Fin n) (Fin n) F) *ᵥ f y) : f = 0 := by
  refine eq_zero_of_natDual_equivariant hn f fun g hg x => ?_
  have H := hf (tinvGL g) (tinvGL_mem_statedSL hg) x
  rw [tinvGL_tinvGL] at H
  exact H

theorem exists_scalars_of_equivariant (hn : 3 ≤ n)
    (f : (Fin n → F) × (Fin n → F) →+ (Fin n → F) × (Fin n → F))
    (hf : ∀ g ∈ StatedSL n F, ∀ p : (Fin n → F) × (Fin n → F),
      f ((g : Matrix (Fin n) (Fin n) F) *ᵥ p.1,
          ((tinvGL g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ p.2) =
        ((g : Matrix (Fin n) (Fin n) F) *ᵥ (f p).1,
          ((tinvGL g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ (f p).2)) :
    ∃ a b : F, ∀ p, f p = (a • p.1, b • p.2) := by
  obtain ⟨f₁₁, h₁₁⟩ : ∃ φ : (Fin n → F) →+ (Fin n → F), ∀ x, φ x = (f (x, 0)).1 :=
    ⟨(AddMonoidHom.fst (Fin n → F) (Fin n → F)).comp
      (f.comp (AddMonoidHom.inl (Fin n → F) (Fin n → F))), fun x => rfl⟩
  obtain ⟨f₂₁, h₂₁⟩ : ∃ φ : (Fin n → F) →+ (Fin n → F), ∀ x, φ x = (f (x, 0)).2 :=
    ⟨(AddMonoidHom.snd (Fin n → F) (Fin n → F)).comp
      (f.comp (AddMonoidHom.inl (Fin n → F) (Fin n → F))), fun x => rfl⟩
  obtain ⟨f₁₂, h₁₂⟩ : ∃ φ : (Fin n → F) →+ (Fin n → F), ∀ y, φ y = (f (0, y)).1 :=
    ⟨(AddMonoidHom.fst (Fin n → F) (Fin n → F)).comp
      (f.comp (AddMonoidHom.inr (Fin n → F) (Fin n → F))), fun y => rfl⟩
  obtain ⟨f₂₂, h₂₂⟩ : ∃ φ : (Fin n → F) →+ (Fin n → F), ∀ y, φ y = (f (0, y)).2 :=
    ⟨(AddMonoidHom.snd (Fin n → F) (Fin n → F)).comp
      (f.comp (AddMonoidHom.inr (Fin n → F) (Fin n → F))), fun y => rfl⟩
  have e₁₁ : ∀ g ∈ StatedSL n F, ∀ x : Fin n → F,
      f₁₁ ((g : Matrix (Fin n) (Fin n) F) *ᵥ x) = (g : Matrix (Fin n) (Fin n) F) *ᵥ f₁₁ x := by
    intro g hg x
    have H : f ((g : Matrix (Fin n) (Fin n) F) *ᵥ x,
        ((tinvGL g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ (0 : Fin n → F)) =
        ((g : Matrix (Fin n) (Fin n) F) *ᵥ (f (x, 0)).1,
          ((tinvGL g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ (f (x, 0)).2) :=
      hf g hg (x, 0)
    rw [Matrix.mulVec_zero] at H
    rw [h₁₁, h₁₁]
    exact congrArg Prod.fst H
  have e₂₁ : ∀ g ∈ StatedSL n F, ∀ x : Fin n → F,
      f₂₁ ((g : Matrix (Fin n) (Fin n) F) *ᵥ x) =
        ((tinvGL g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ f₂₁ x := by
    intro g hg x
    have H : f ((g : Matrix (Fin n) (Fin n) F) *ᵥ x,
        ((tinvGL g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ (0 : Fin n → F)) =
        ((g : Matrix (Fin n) (Fin n) F) *ᵥ (f (x, 0)).1,
          ((tinvGL g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ (f (x, 0)).2) :=
      hf g hg (x, 0)
    rw [Matrix.mulVec_zero] at H
    rw [h₂₁, h₂₁]
    exact congrArg Prod.snd H
  have e₁₂ : ∀ g ∈ StatedSL n F, ∀ y : Fin n → F,
      f₁₂ (((tinvGL g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ y) =
        (g : Matrix (Fin n) (Fin n) F) *ᵥ f₁₂ y := by
    intro g hg y
    have H : f ((g : Matrix (Fin n) (Fin n) F) *ᵥ (0 : Fin n → F),
        ((tinvGL g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ y) =
        ((g : Matrix (Fin n) (Fin n) F) *ᵥ (f (0, y)).1,
          ((tinvGL g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ (f (0, y)).2) :=
      hf g hg (0, y)
    rw [Matrix.mulVec_zero] at H
    rw [h₁₂, h₁₂]
    exact congrArg Prod.fst H
  have e₂₂ : ∀ g ∈ StatedSL n F, ∀ y : Fin n → F,
      f₂₂ (((tinvGL g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ y) =
        ((tinvGL g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ f₂₂ y := by
    intro g hg y
    have H : f ((g : Matrix (Fin n) (Fin n) F) *ᵥ (0 : Fin n → F),
        ((tinvGL g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ y) =
        ((g : Matrix (Fin n) (Fin n) F) *ᵥ (f (0, y)).1,
          ((tinvGL g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ (f (0, y)).2) :=
      hf g hg (0, y)
    rw [Matrix.mulVec_zero] at H
    rw [h₂₂, h₂₂]
    exact congrArg Prod.snd H
  have hz21 : f₂₁ = 0 := eq_zero_of_natDual_equivariant hn f₂₁ e₂₁
  have hz12 : f₁₂ = 0 := eq_zero_of_dualNat_equivariant hn f₁₂ e₁₂
  obtain ⟨a, ha⟩ := addCommutantScalar_statedSL (K := F) (by omega : 2 ≤ n) f₁₁ e₁₁
  have e₂₂' : ∀ h ∈ StatedSL n F, ∀ y : Fin n → F,
      f₂₂ ((h : Matrix (Fin n) (Fin n) F) *ᵥ y) = (h : Matrix (Fin n) (Fin n) F) *ᵥ f₂₂ y := by
    intro h hh y
    have H := e₂₂ (tinvGL h) (tinvGL_mem_statedSL hh) y
    rw [tinvGL_tinvGL] at H
    exact H
  obtain ⟨b, hb⟩ := addCommutantScalar_statedSL (K := F) (by omega : 2 ≤ n) f₂₂ e₂₂'
  refine ⟨a, b, fun p => ?_⟩
  obtain ⟨x, y⟩ := p
  show f (x, y) = (a • x, b • y)
  have hA1 : (f (x, 0)).1 = a • x := by rw [← h₁₁ x, ha x]
  have hA2 : (f (x, 0)).2 = 0 := by
    rw [← h₂₁ x]
    simp [hz21]
  have hB1 : (f (0, y)).1 = 0 := by
    rw [← h₁₂ y]
    simp [hz12]
  have hB2 : (f (0, y)).2 = b • y := by rw [← h₂₂ y, hb y]
  have hX : f (x, 0) = (a • x, 0) := Prod.ext hA1 hA2
  have hY : f (0, y) = (0, b • y) := Prod.ext hB1 hB2
  have hxy : f (x, y) = f (x, 0) + f (0, y) := by
    rw [← map_add, Prod.mk_add_mk, add_zero, zero_add]
  rw [hxy, hX, hY, Prod.mk_add_mk, add_zero, zero_add]

end CFSG.RankThree.GF2n.Stroth80
