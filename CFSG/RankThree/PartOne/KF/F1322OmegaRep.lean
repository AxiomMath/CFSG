module

public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.Combinatorics.Matroid.Init
public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.RankThree.PartOne.KF1322

open Matrix Module Polynomial

theorem exists_orth_vec_of_value {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {M : Matrix (Fin 3) (Fin 3) (ZMod p)} (hMt : Mᵀ = M) (hdet : M.det ≠ 0)
    {r : Fin 3 → ZMod p} (hr : r ⬝ᵥ (M *ᵥ r) ≠ 0) (β : ZMod p) :
    ∃ f : Fin 3 → ZMod p, r ⬝ᵥ (M *ᵥ f) = 0 ∧ f ⬝ᵥ (M *ᵥ f) = β := by
  classical
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp this)
  have : Invertible (2 : ZMod p) := invertibleOfNonzero h2
  set B : LinearMap.BilinForm (ZMod p) (Fin 3 → ZMod p) := Matrix.toBilin' M with hB
  have hBapp : ∀ u v, B u v = u ⬝ᵥ (M *ᵥ v) := fun u v => Matrix.toBilin'_apply' M u v
  have hnd : B.Nondegenerate := LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero.mpr hdet
  have hsymmEq : ∀ u v, B u v = B v u := by
    intro u v
    rw [hBapp, hBapp]
    calc u ⬝ᵥ M *ᵥ v = u ᵥ* M ⬝ᵥ v := Matrix.dotProduct_mulVec _ _ _
      _ = u ᵥ* Mᵀ ⬝ᵥ v := by rw [hMt]
      _ = M *ᵥ u ⬝ᵥ v := by rw [Matrix.vecMul_transpose]
      _ = v ⬝ᵥ M *ᵥ u := dotProduct_comm _ _
  have hsymm : B.IsSymm := ⟨hsymmEq⟩
  have hsymm' : LinearMap.IsSymm B := LinearMap.BilinForm.isSymm_iff.mp hsymm
  have hrefl : B.IsRefl := hsymm.isRefl
  have hrr : B r r ≠ 0 := by rw [hBapp]; exact hr
  have hrne : r ≠ 0 := by
    rintro rfl
    apply hr
    exact zero_dotProduct _
  set U := B.orthogonal (ZMod p ∙ r) with hU
  have hUnd : (B.restrict U).Nondegenerate :=
    LinearMap.BilinForm.restrict_nondegenerate_orthogonal_spanSingleton B hnd hrefl hrr
  have hfin : finrank (ZMod p) U = 2 := by
    have := Submodule.finrank_add_eq_of_isCompl
      (LinearMap.BilinForm.isCompl_span_singleton_orthogonal hrr)
    rw [finrank_span_singleton hrne, Module.finrank_fin_fun] at this
    show finrank (ZMod p) (B.orthogonal (ZMod p ∙ r)) = 2
    omega
  have hUsymm : LinearMap.IsSymm (B.restrict U) := ⟨fun x y => hsymmEq x y⟩
  obtain ⟨v, hv⟩ := LinearMap.BilinForm.exists_orthogonal_basis hUsymm
  have hne : ∀ i, B (v i : Fin 3 → ZMod p) (v i : Fin 3 → ZMod p) ≠ 0 := fun i =>
    hv.not_isOrtho_basis_self_of_separatingLeft hUnd.1 i
  let i₀ : Fin (finrank (ZMod p) U) := ⟨0, by omega⟩
  let i₁ : Fin (finrank (ZMod p) U) := ⟨1, by omega⟩
  have hi : i₀ ≠ i₁ := by simp [i₀, i₁, Fin.ext_iff]
  have hg12 : B (v i₀ : Fin 3 → ZMod p) (v i₁ : Fin 3 → ZMod p) = 0 := hv hi
  have hg21 : B (v i₁ : Fin 3 → ZMod p) (v i₀ : Fin 3 → ZMod p) = 0 := by
    rw [hsymmEq]; exact hg12
  have hrg : ∀ i, B r (v i : Fin 3 → ZMod p) = 0 := by
    intro i
    have := (LinearMap.BilinForm.mem_orthogonal_iff.mp (v i).2) r (Submodule.mem_span_singleton_self r)
    exact this
  set g₁ : Fin 3 → ZMod p := (v i₀ : Fin 3 → ZMod p) with hg₁
  set g₂ : Fin 3 → ZMod p := (v i₁ : Fin 3 → ZMod p) with hg₂
  have hc₁ : B g₁ g₁ ≠ 0 := hne i₀
  have hc₂ : B g₂ g₂ ≠ 0 := hne i₁
  have hodd : Fintype.card (ZMod p) % 2 = 1 := by
    rw [ZMod.card]
    rcases (Fact.out : p.Prime).eq_two_or_odd with h | h
    · exact absurd h hp2
    · exact h
  have hdeg1 : degree (C (B g₁ g₁) * X ^ 2 : (ZMod p)[X]) = 2 := by
    rw [degree_C_mul_X_pow 2 hc₁]
    rfl
  have hdeg2 : degree (C (B g₂ g₂) * X ^ 2 - C β : (ZMod p)[X]) = 2 := by
    have h1 : degree (C (B g₂ g₂) * X ^ 2 : (ZMod p)[X]) = 2 := by
      rw [degree_C_mul_X_pow 2 hc₂]
      rfl
    rw [degree_sub_C (by rw [h1]; norm_num), h1]
  obtain ⟨a, b, hab⟩ := FiniteField.exists_root_sum_quadratic hdeg1 hdeg2 hodd
  simp only [eval_mul, eval_C, eval_pow, eval_X, eval_sub] at hab
  have hrg₁ : B r g₁ = 0 := hrg i₀
  have hrg₂ : B r g₂ = 0 := hrg i₁
  refine ⟨a • g₁ + b • g₂, ?_, ?_⟩
  · rw [← hBapp]
    simp only [map_add, map_smul, smul_eq_mul, hrg₁, hrg₂]
    ring
  · rw [← hBapp]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hg12,
      hg21]
    linear_combination hab

end CFSG.RankThree.PartOne.KF1322
