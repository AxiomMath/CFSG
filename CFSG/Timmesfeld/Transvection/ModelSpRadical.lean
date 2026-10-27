module

public import CFSG.Timmesfeld.Transvection.ModelRadical

public section

namespace CFSG.Timmesfeld.Transvection

open Matrix CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.Universal.Symplectic
  CFSG.Timmesfeld.ARS CFSG.Timmesfeld.ARS.CaseM

namespace ModelRank

section Param

variable {n : ℕ} {F : Type} [Field F]

theorem spForm_zero_left (v : Fin n ⊕ Fin n → F) : spForm 0 v = 0 := by
  simp [spForm]

theorem spForm_zero_right (v : Fin n ⊕ Fin n → F) : spForm v 0 = 0 := by
  simp [spForm]

theorem exists_spForm_eq_one {a : Fin n ⊕ Fin n → F} (ha : a ≠ 0) :
    ∃ v₀ : Fin n ⊕ Fin n → F, spForm a v₀ = 1 := by
  obtain ⟨y, hy⟩ := exists_spForm_ne_zero ha
  exact ⟨(spForm a y)⁻¹ • y, by rw [spForm_smul_right', inv_mul_cancel₀ hy]⟩

theorem spTrans_mulVec_param (a v : Fin n ⊕ Fin n → F) (e : F) :
    spTrans a e *ᵥ v = v + spForm a v • (0 : Fin n ⊕ Fin n → F) +
      spForm (0 : Fin n ⊕ Fin n → F) v • a + (e * spForm a v) • a := by
  rw [spTrans_mulVec, spForm_zero_left, smul_zero, zero_smul, add_zero, add_zero]

theorem mat_eq_spTrans_of_param [CharP F 2] {a w : Fin n ⊕ Fin n → F} {l c : F}
    {x : StatedSp n F} (hx : ∀ v, SpExtras.mat n F x *ᵥ v =
      v + spForm a v • w + spForm w v • a + (l * spForm a v) • a)
    (hw : w = c • a) : SpExtras.mat n F x = spTrans a l := by
  refine Matrix.ext_iff_mulVec.2 fun v => ?_
  rw [hx, spTrans_mulVec, hw, spForm_smul_left']
  have h2 := two_smul_vec_eq_zero ((c * spForm a v) • a)
  linear_combination (norm := module) h2

theorem mat_mul_mulVec_of_param {a w w' : Fin n ⊕ Fin n → F} {l l' : F} {x y : StatedSp n F}
    (haw : spForm a w = 0) (haw' : spForm a w' = 0)
    (hx : ∀ v, SpExtras.mat n F x *ᵥ v =
      v + spForm a v • w + spForm w v • a + (l * spForm a v) • a)
    (hy : ∀ v, SpExtras.mat n F y *ᵥ v =
      v + spForm a v • w' + spForm w' v • a + (l' * spForm a v) • a)
    (v : Fin n ⊕ Fin n → F) :
    SpExtras.mat n F (x * y) *ᵥ v = v + spForm a v • (w + w') + spForm (w + w') v • a +
      ((l + l' + spForm w w') * spForm a v) • a := by
  have hwa : spForm w a = 0 := spForm_eq_zero_comm haw
  rw [map_mul, ← mulVec_mulVec, hy v, hx]
  simp only [spForm_add_left, spForm_add_right, spForm_smul_right', haw', hwa, spForm_self,
    mul_zero, add_zero]
  module

theorem mat_conj_mulVec_of_param {a w : Fin n ⊕ Fin n → F} {l : F} {x g : StatedSp n F}
    (hx : ∀ v, SpExtras.mat n F x *ᵥ v =
      v + spForm a v • w + spForm w v • a + (l * spForm a v) • a)
    (hga : SpExtras.mat n F g *ᵥ a = a) (v : Fin n ⊕ Fin n → F) :
    SpExtras.mat n F (g * x * g⁻¹) *ᵥ v = v + spForm a v • (SpExtras.mat n F g *ᵥ w) +
      spForm (SpExtras.mat n F g *ᵥ w) v • a + (l * spForm a v) • a := by
  have h1 : spForm a (SpExtras.mat n F g⁻¹ *ᵥ v) = spForm a v := by
    have h := spForm_mat_mulVec g a (SpExtras.mat n F g⁻¹ *ᵥ v)
    rw [hga, mat_mulVec_mat_inv_mulVec] at h
    exact h.symm
  have h2 : spForm w (SpExtras.mat n F g⁻¹ *ᵥ v) = spForm (SpExtras.mat n F g *ᵥ w) v := by
    have h := spForm_mat_mulVec g w (SpExtras.mat n F g⁻¹ *ᵥ v)
    rw [mat_mulVec_mat_inv_mulVec] at h
    exact h.symm
  rw [map_mul, map_mul, ← mulVec_mulVec, ← mulVec_mulVec, hx, h1, h2, mulVec_add, mulVec_add,
    mulVec_add, mulVec_smul, mulVec_smul, mulVec_smul, mat_mulVec_mat_inv_mulVec, hga]

theorem exists_eq_add_smul_of_param {a w₁ w₂ : Fin n ⊕ Fin n → F} {l₁ l₂ : F}
    {x : StatedSp n F} (ha : a ≠ 0)
    (h₁ : ∀ v, SpExtras.mat n F x *ᵥ v =
      v + spForm a v • w₁ + spForm w₁ v • a + (l₁ * spForm a v) • a)
    (h₂ : ∀ v, SpExtras.mat n F x *ᵥ v =
      v + spForm a v • w₂ + spForm w₂ v • a + (l₂ * spForm a v) • a) :
    ∃ c : F, w₁ = w₂ + c • a := by
  obtain ⟨v₀, hv₀⟩ := exists_spForm_eq_one ha
  have h := (h₁ v₀).symm.trans (h₂ v₀)
  simp only [hv₀, one_smul, mul_one] at h
  exact ⟨spForm w₂ v₀ + l₂ - spForm w₁ v₀ - l₁, by linear_combination (norm := module) h⟩

end Param

theorem exists_param_of_mem_spRad {n : ℕ} {F : Type} [Field F] [CharP F 2]
    {a : Fin n ⊕ Fin n → F} (ha : a ≠ 0) {x : StatedSp n F} (hx : x ∈ spRad a) :
    ∃ (w : Fin n ⊕ Fin n → F) (l : F), spForm a w = 0 ∧ ∀ v : Fin n ⊕ Fin n → F,
      SpExtras.mat n F x *ᵥ v = v + spForm a v • w + spForm w v • a + (l * spForm a v) • a := by
  obtain ⟨hxa, hxu⟩ := hx
  obtain ⟨v₀, hv₀⟩ := exists_spForm_eq_one ha
  have hv₀a : spForm v₀ a = 1 := by rw [spForm_comm, CharTwo.neg_eq, hv₀]
  obtain ⟨w, hw⟩ : ∃ w, w = SpExtras.mat n F x *ᵥ v₀ + v₀ := ⟨_, rfl⟩
  have hxv₀ : SpExtras.mat n F x *ᵥ v₀ = w + v₀ := by
    rw [hw, add_assoc, vec_add_self, add_zero]
  have haw : spForm a w = 0 := by
    have h := spForm_mat_mulVec x a v₀
    rw [hxa] at h
    rw [hw, spForm_add_right, h, hv₀, CharTwo.add_self_eq_zero]
  have hwa : spForm w a = 0 := spForm_eq_zero_comm haw
  refine ⟨w, spForm w v₀, haw, fun v => ?_⟩
  obtain ⟨u, hu⟩ : ∃ u, u = v + spForm a v • v₀ := ⟨_, rfl⟩
  have hv : v = u + spForm a v • v₀ := by
    rw [hu, add_assoc, vec_add_self, add_zero]
  have hau : spForm a u = 0 := by
    rw [hu, spForm_add_right, spForm_smul_right', hv₀, mul_one, CharTwo.add_self_eq_zero]
  obtain ⟨c, hc⟩ := hxu u hau
  have hcu : c = spForm w u := by
    have h := spForm_mat_mulVec x v₀ u
    rw [hxv₀, hc] at h
    simp only [spForm_add_left, spForm_add_right, spForm_smul_right', hwa, hv₀a] at h
    linear_combination h - spForm w u * (CharTwo.two_eq_zero : (2 : F) = 0)
  have hwu : spForm w u = spForm w v + spForm w v₀ * spForm a v := by
    rw [hu, spForm_add_right, spForm_smul_right', mul_comm]
  have hxv : SpExtras.mat n F x *ᵥ v = u + c • a + spForm a v • (w + v₀) := by
    rw [← hc, ← hxv₀, ← mulVec_smul, ← mulVec_add, ← hv]
  rw [hxv, hcu, hwu, hu]
  have h2 := two_smul_vec_eq_zero (spForm a v • v₀)
  linear_combination (norm := module) h2

theorem spRadCommStmt_holds {n : ℕ} {F : Type} [Field F] [CharP F 2] : SpRadCommStmt n F := by
  intro a ha x hx y hy
  obtain ⟨w, l, haw, hxw⟩ := exists_param_of_mem_spRad ha hx
  obtain ⟨w', l', haw', hyw⟩ := exists_param_of_mem_spRad ha hy
  have hww' : spForm w' w = spForm w w' := by rw [spForm_comm, CharTwo.neg_eq]
  refine eq_of_mat_mulVec_eq fun v => ?_
  rw [mat_mul_mulVec_of_param haw haw' hxw hyw, mat_mul_mulVec_of_param haw' haw hyw hxw,
    add_comm w' w, add_comm l' l, hww']

end ModelRank

end CFSG.Timmesfeld.Transvection
