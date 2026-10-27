module

public import CFSG.Quasithin.Background.F7TwoInvSp4OddTorus

public section

namespace CFSG.Quasithin.F7Two

open Matrix CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain

variable {K : Type} [Field K] [CharP K 2]

@[expose] noncomputable def tvGL (v : Fin 4 → K) (t : K) : GL (Fin 4) K :=
  GeneralLinearGroup.toLin.symm (CFSG.ClassicalGroups.Alternating.symplecticTransvection
    (minorForm K) minorForm_isAlt v t)

theorem tvGL_mem (v : Fin 4 → K) (t : K) : tvGL v t ∈ antiSp K := by
  rw [antiSp_eq_closure]
  exact Subgroup.subset_closure ⟨v, t, rfl⟩

theorem glMat_tvGL (v : Fin 4 → K) (t : K) : glMat (tvGL v t) = transvMat v t :=
  glMat_transvection v t

@[expose] noncomputable def tvElt (v : Fin 4 → K) (t : K) : antiSp K := ⟨tvGL v t, tvGL_mem v t⟩

theorem glMat_tvElt (v : Fin 4 → K) (t : K) : glMat (tvElt v t : antiSp K).1 = transvMat v t :=
  glMat_tvGL v t

omit [CharP K 2] in
theorem transvMat_mulVec (v : Fin 4 → K) (t : K) (x : Fin 4 → K) :
    transvMat v t *ᵥ x = x + (t * minorForm K x v) • v := by
  ext i
  fin_cases i <;>
    simp [transvMat, minorForm_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_four] <;> ring

omit [CharP K 2] in
theorem minorForm_mulVec {M : Matrix (Fin 4) (Fin 4) K} (hM : Mᵀ * minorJ K * M = minorJ K)
    (x y : Fin 4 → K) : minorForm K (M *ᵥ x) (M *ᵥ y) = minorForm K x y := by
  have h : minorForm K (M *ᵥ x) (M *ᵥ y) = Matrix.toBilin' (Mᵀ * minorJ K * M) x y := by
    rw [← Matrix.toBilin'_comp]
    rfl
  rw [h, hM]

omit [CharP K 2] in
theorem mul_transvMat_eq {M : Matrix (Fin 4) (Fin 4) K} (hM : Mᵀ * minorJ K * M = minorJ K)
    (v : Fin 4 → K) (t : K) : M * transvMat v t = transvMat (M *ᵥ v) t * M := by
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun x => ?_
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    transvMat_mulVec, transvMat_mulVec, Matrix.mulVec_add, Matrix.mulVec_smul,
    minorForm_mulVec hM]

theorem mul_tvElt_mul_inv (g : antiSp K) (v : Fin 4 → K) (t : K) :
    g * tvElt v t * g⁻¹ = tvElt (glMat (g : GL (Fin 4) K) *ᵥ v) t := by
  rw [mul_inv_eq_iff_eq_mul]
  refine antiSp_ext ?_
  have h1 : glMat ((g * tvElt v t : antiSp K) : GL (Fin 4) K) =
      glMat (g : GL (Fin 4) K) * transvMat v t := by
    rw [← glMat_tvElt]
    rfl
  have h2 : glMat ((tvElt (glMat (g : GL (Fin 4) K) *ᵥ v) t * g : antiSp K) : GL (Fin 4) K) =
      transvMat (glMat (g : GL (Fin 4) K) *ᵥ v) t * glMat (g : GL (Fin 4) K) := by
    rw [← glMat_tvElt]
    rfl
  rw [h1, h2]
  exact mul_transvMat_eq (mem_antiSp.mp g.2) v t

theorem tvElt_smul (r : K) (v : Fin 4 → K) (t : K) : tvElt (r • v) t = tvElt v (t * r ^ 2) := by
  refine antiSp_ext ?_
  rw [glMat_tvElt, glMat_tvElt]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [transvMat] <;> ring

theorem tvElt_single_zero (t : K) : tvElt (Pi.single 0 1 : Fin 4 → K) t = uElt 0 0 t 0 := by
  refine antiSp_ext ?_
  rw [glMat_tvElt, glMat_uElt]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [transvMat, uMat]

@[expose] def TvIn (H : Subgroup (antiSp K)) (v : Fin 4 → K) : Prop := ∀ t, tvElt v t ∈ H

variable {H : Subgroup (antiSp K)} {v : Fin 4 → K}

theorem TvIn.smul (hv : TvIn H v) (r : K) : TvIn H (r • v) := fun t => by
  rw [tvElt_smul]
  exact hv _

theorem TvIn.conj (hv : TvIn H v) {h : antiSp K} (hh : h ∈ H) :
    TvIn H (glMat (h : GL (Fin 4) K) *ᵥ v) := fun t => by
  rw [← mul_tvElt_mul_inv]
  exact H.mul_mem (H.mul_mem hh (hv t)) (H.inv_mem hh)

theorem TvIn.of_apply {u : antiSp K} (hu : u ∈ H) (hv : TvIn H (glMat (u : GL (Fin 4) K) *ᵥ v)) :
    TvIn H v := by
  have h1 := hv.conj (H.inv_mem hu)
  rwa [Matrix.mulVec_mulVec, show glMat ((u⁻¹ : antiSp K) : GL (Fin 4) K) *
    glMat (u : GL (Fin 4) K) = 1 from (u : GL (Fin 4) K).inv_mul, Matrix.one_mulVec] at h1

theorem glMat_jElt_uElt_mulVec (a b c : K) :
    glMat ((jElt * uElt a b c 0 * jElt⁻¹ : antiSp K) : GL (Fin 4) K) *ᵥ Pi.single 0 1 =
      ![1, a, b, c] := by
  change (minorJ K * uMat a b c 0 * minorJ K) *ᵥ Pi.single 0 1 = _
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Matrix.mul_apply, Fin.sum_univ_four,
    minorJ_apply, uMat]

theorem eq_top_of_uElt_le (H : Subgroup (antiSp K)) (hU : ∀ a b c d : K, uElt a b c d ∈ H)
    (hL : ∀ a b c d : K, jElt * uElt a b c d * jElt⁻¹ ∈ H) : H = ⊤ := by
  have he0 : TvIn H (Pi.single 0 1 : Fin 4 → K) := fun t => by
    rw [tvElt_single_zero]
    exact hU 0 0 t 0
  have h1 : ∀ v : Fin 4 → K, v 0 ≠ 0 → TvIn H v := by
    intro v hv0
    have hmem := hL (v 1 / v 0) (v 2 / v 0) (v 3 / v 0) 0
    have h2 := (he0.conj hmem).smul (v 0)
    rw [glMat_jElt_uElt_mulVec] at h2
    convert h2 using 1
    ext i
    fin_cases i <;> simp <;> field_simp
  have h3 : ∀ v : Fin 4 → K, TvIn H v := by
    intro v
    by_cases hv0 : v 0 = 0
    · by_cases hv1 : v 1 = 0
      · by_cases hv2 : v 2 = 0
        · by_cases hv3 : v 3 = 0
          · have : v = 0 := by
              ext i
              fin_cases i <;> simp [hv0, hv1, hv2, hv3]
            rw [this]
            intro t
            have : tvElt (0 : Fin 4 → K) t = 1 := by
              refine antiSp_ext ?_
              rw [glMat_tvElt]
              ext i j
              fin_cases i <;> fin_cases j <;> simp [transvMat]
            rw [this]
            exact H.one_mem
          · refine TvIn.of_apply (hU 0 0 1 0) (h1 _ ?_)
            simp [glMat_uElt, uMat, Matrix.mulVec, dotProduct, Fin.sum_univ_four, hv0, hv3]
        · refine TvIn.of_apply (hU 0 1 0 0) (h1 _ ?_)
          simp [glMat_uElt, uMat, Matrix.mulVec, dotProduct, Fin.sum_univ_four, hv0, hv2]
      · refine TvIn.of_apply (hU 1 0 0 0) (h1 _ ?_)
        simp [glMat_uElt, uMat, Matrix.mulVec, dotProduct, Fin.sum_univ_four, hv0, hv1]
    · exact h1 v hv0
  rw [eq_top_iff]
  intro g _
  have hS := antiSp_eq_closure (K := K)
  have key : ∀ x ∈ Subgroup.closure {g | ∃ (v : Fin 4 → K) (t : K),
      g = GeneralLinearGroup.toLin.symm (CFSG.ClassicalGroups.Alternating.symplecticTransvection
        (minorForm K) minorForm_isAlt v t)}, ∀ hx : x ∈ antiSp K, (⟨x, hx⟩ : antiSp K) ∈ H := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      intro hx'
      obtain ⟨v, t, rfl⟩ := hx
      exact h3 v t
    | one => intro h1; exact H.one_mem
    | mul x y hx hy ihx ihy =>
      intro hxy
      have hx' : x ∈ antiSp K := hS ▸ hx
      have hy' : y ∈ antiSp K := hS ▸ hy
      exact H.mul_mem (ihx hx') (ihy hy')
    | inv x hx ihx =>
      intro hxi
      have hx' : x ∈ antiSp K := hS ▸ hx
      exact H.inv_mem (ihx hx')
  exact key g.1 (hS ▸ g.2) g.2

end CFSG.Quasithin.F7Two
