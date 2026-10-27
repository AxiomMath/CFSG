module

public import CFSG.Quasithin.Vol2.Ch4Sec2CentKLinStab
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.Quasithin.H13.Ch4.CentK

open Matrix

variable {F : Type} [Field F]

private def crossProdCoord (w u : Fin 3 → F) : Fin 3 → F :=
  ![w 1 * u 2 - w 2 * u 1, w 2 * u 0 - w 0 * u 2, w 0 * u 1 - w 1 * u 0]

private theorem exists_stabVec_sub_eq {w x u c : Fin 3 → F}
    (hcw : c ⬝ᵥ w = 0) (hcu : c ⬝ᵥ u = 0) (hcx : c ⬝ᵥ x ≠ 0) :
    ∃ g ∈ stabVec w, (g : Matrix (Fin 3) (Fin 3) F) *ᵥ x - x = u := by
  obtain ⟨κ, hκ⟩ : ∃ κ : F, κ * (c ⬝ᵥ x) = 1 := ⟨(c ⬝ᵥ x)⁻¹, inv_mul_cancel₀ hcx⟩
  obtain ⟨M, hM⟩ : ∃ M : Matrix (Fin 3) (Fin 3) F,
      M = !![1 + u 0 * (κ * c 0), u 0 * (κ * c 1), u 0 * (κ * c 2);
        u 1 * (κ * c 0), 1 + u 1 * (κ * c 1), u 1 * (κ * c 2);
        u 2 * (κ * c 0), u 2 * (κ * c 1), 1 + u 2 * (κ * c 2)] := ⟨_, rfl⟩
  have key : ∀ v : Fin 3 → F, M *ᵥ v = v + (κ * (c ⬝ᵥ v)) • u := by
    intro v
    funext i
    rw [hM]
    fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_three] <;> ring
  have hcu' : c 0 * u 0 + c 1 * u 1 + c 2 * u 2 = 0 := by
    simpa [dotProduct, Fin.sum_univ_three] using hcu
  have hdet : M.det = 1 := by
    rw [hM, det_fin_three]
    simp
    linear_combination κ * hcu'
  obtain ⟨g, hgM⟩ : ∃ g : SpecialLinearGroup (Fin 3) F, (g : Matrix (Fin 3) (Fin 3) F) = M :=
    ⟨⟨M, hdet⟩, rfl⟩
  refine ⟨g, ?_, ?_⟩
  · rw [mem_stabVec, hgM, key, hcw, mul_zero, zero_smul, add_zero]
  · rw [hgM, key, hκ, one_smul, add_sub_cancel_left]

theorem span_stabVec [Fintype F] (h4 : 4 ≤ Fintype.card F) {w : Fin 3 → F} (hw : w ≠ 0)
    (ℓ : Submodule F (Fin 3 → F)) (hℓ : Module.finrank F ℓ = 2) :
    AddSubgroup.closure {y : Fin 3 → F | ∃ g ∈ stabVec w, ∃ x ∈ ℓ,
      y = (g : Matrix (Fin 3) (Fin 3) F).mulVec x - x} = ⊤ := by
  obtain ⟨x, hxℓ, hxw⟩ : ∃ x ∈ ℓ, x ∉ Submodule.span F {w} := by
    by_contra hcon
    push Not at hcon
    have hle : ℓ ≤ Submodule.span F {w} := fun x hx => hcon x hx
    have h1 := Submodule.finrank_mono hle
    rw [finrank_span_singleton hw, hℓ] at h1
    omega
  set A := AddSubgroup.closure {y : Fin 3 → F | ∃ g ∈ stabVec w, ∃ x ∈ ℓ,
      y = (g : Matrix (Fin 3) (Fin 3) F).mulVec x - x} with hA
  have hmem : ∀ u : Fin 3 → F, crossProdCoord w u ⬝ᵥ x ≠ 0 → u ∈ A := by
    intro u hu
    have hcw : crossProdCoord w u ⬝ᵥ w = 0 := by
      simp [crossProdCoord, dotProduct, Fin.sum_univ_three] <;> ring
    have hcu : crossProdCoord w u ⬝ᵥ u = 0 := by
      simp [crossProdCoord, dotProduct, Fin.sum_univ_three] <;> ring
    obtain ⟨g, hg, hgu⟩ :=
      exists_stabVec_sub_eq (x := x) (u := u) (c := crossProdCoord w u) hcw hcu hu
    rw [← hgu]
    apply AddSubgroup.subset_closure
    exact ⟨g, hg, x, hxℓ, rfl⟩
  have hadd : ∀ u z : Fin 3 → F,
      crossProdCoord w (u + z) ⬝ᵥ x = crossProdCoord w u ⬝ᵥ x + crossProdCoord w z ⬝ᵥ x := by
    intro u z
    simp [crossProdCoord, dotProduct, Fin.sum_univ_three] <;> ring
  obtain ⟨z, hz⟩ : ∃ z : Fin 3 → F, crossProdCoord w z ⬝ᵥ x ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hxw
    have E0 : x 1 * w 2 - x 2 * w 1 = 0 := by
      have h := hcon ![1, 0, 0]
      simp [crossProdCoord, dotProduct, Fin.sum_univ_three] at h
      linear_combination h
    have E1 : x 2 * w 0 - x 0 * w 2 = 0 := by
      have h := hcon ![0, 1, 0]
      simp [crossProdCoord, dotProduct, Fin.sum_univ_three] at h
      linear_combination h
    have E2 : x 0 * w 1 - x 1 * w 0 = 0 := by
      have h := hcon ![0, 0, 1]
      simp [crossProdCoord, dotProduct, Fin.sum_univ_three] at h
      linear_combination h
    obtain ⟨j, hj⟩ : ∃ j, w j ≠ 0 := by
      by_contra h
      push Not at h
      exact hw (funext h)
    rw [Submodule.mem_span_singleton]
    fin_cases j
    · have hj' : w 0 ≠ 0 := hj
      refine ⟨x 0 / w 0, ?_⟩
      funext i
      fin_cases i
      · show x 0 / w 0 * w 0 = x 0
        exact div_mul_cancel₀ _ hj'
      · show x 0 / w 0 * w 1 = x 1
        rw [div_mul_eq_mul_div, div_eq_iff hj']
        linear_combination E2
      · show x 0 / w 0 * w 2 = x 2
        rw [div_mul_eq_mul_div, div_eq_iff hj']
        linear_combination -E1
    · have hj' : w 1 ≠ 0 := hj
      refine ⟨x 1 / w 1, ?_⟩
      funext i
      fin_cases i
      · show x 1 / w 1 * w 0 = x 0
        rw [div_mul_eq_mul_div, div_eq_iff hj']
        linear_combination -E2
      · show x 1 / w 1 * w 1 = x 1
        exact div_mul_cancel₀ _ hj'
      · show x 1 / w 1 * w 2 = x 2
        rw [div_mul_eq_mul_div, div_eq_iff hj']
        linear_combination E0
    · have hj' : w 2 ≠ 0 := hj
      refine ⟨x 2 / w 2, ?_⟩
      funext i
      fin_cases i
      · show x 2 / w 2 * w 0 = x 0
        rw [div_mul_eq_mul_div, div_eq_iff hj']
        linear_combination E1
      · show x 2 / w 2 * w 1 = x 1
        rw [div_mul_eq_mul_div, div_eq_iff hj']
        linear_combination -E0
      · show x 2 / w 2 * w 2 = x 2
        exact div_mul_cancel₀ _ hj'
  refine eq_top_iff.mpr fun u _ => ?_
  by_cases hu : crossProdCoord w u ⬝ᵥ x = 0
  ·
    have h1 : u + z ∈ A := hmem (u + z) (by rw [hadd, hu, zero_add]; exact hz)
    have h2 : z ∈ A := hmem z hz
    have h3 := A.sub_mem h1 h2
    rwa [add_sub_cancel_right] at h3
  · exact hmem u hu


end CFSG.Quasithin.H13.Ch4.CentK
