module

public import CFSG.Open.StatedDefs
import CFSG.Open.StatedAPI
import CFSG.LinearAlgebra.LinearGroups.Generation
public import Mathlib.LinearAlgebra.Matrix.Notation
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen4FNtL34GenAux1

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open
open Matrix
open scoped CharTwo
open scoped commutatorElement

variable {K : Type} [Field K] [Finite K] [CharP K 2]

private noncomputable def w183_glOfDet (A : Matrix (Fin 3) (Fin 3) K) (h : A.det = 1) :
    GL (Fin 3) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero A (by rw [h]; exact one_ne_zero)

private noncomputable def w183_Pgl : GL (Fin 3) K :=
  w183_glOfDet (w183_Pm (K := K)) w183_Pm_det

private noncomputable def w183_Bgl (ω : K) : GL (Fin 3) K :=
  w183_glOfDet (w183_Bm ω) (w183_Bm_det ω)

private theorem w183_Pgl_val : (w183_Pgl (K := K) : Matrix (Fin 3) (Fin 3) K) = w183_Pm := by
  rw [w183_Pgl, w183_glOfDet]; rfl

private theorem w183_Bgl_val (ω : K) :
    (w183_Bgl ω : Matrix (Fin 3) (Fin 3) K) = w183_Bm ω := by
  rw [w183_Bgl, w183_glOfDet]; rfl

private def w183_tv (i j : Fin 3) (hij : i ≠ j) (c : K) : GL (Fin 3) K :=
  SpecialLinearGroup.toGL (SpecialLinearGroup.transvection hij c)

private theorem w183_tv_val (i j : Fin 3) (hij : i ≠ j) (c : K) :
    (w183_tv i j hij c : Matrix (Fin 3) (Fin 3) K) = Matrix.transvection i j c := rfl

private theorem w183_tv01_val (c : K) :
    (w183_tv 0 1 (by decide) c : Matrix (Fin 3) (Fin 3) K) =
      !![1, c, 0; 0, 1, 0; 0, 0, 1] := by
  rw [w183_tv_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.transvection]

private theorem w183_Pgl_cube : (w183_Pgl (K := K)) ^ 3 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_one, w183_Pgl_val, w183_Pm_cube]

private theorem w183_Bgl_cube (ω : K) (hω : ω ^ 2 = ω + 1) : (w183_Bgl ω) ^ 3 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_one, w183_Bgl_val, w183_Bm_cube ω hω]

private theorem w183_Pgl_inv : (w183_Pgl (K := K))⁻¹ = w183_Pgl (K := K) ^ 2 := by
  have h : w183_Pgl (K := K) ^ 2 * w183_Pgl (K := K) = 1 := by
    have := w183_Pgl_cube (K := K)
    rwa [pow_succ] at this
  exact inv_eq_of_mul_eq_one_left h

private theorem w183_Bgl_inv (ω : K) (hω : ω ^ 2 = ω + 1) :
    (w183_Bgl ω)⁻¹ = w183_Bgl ω ^ 2 := by
  have h : w183_Bgl ω ^ 2 * w183_Bgl ω = 1 := by
    have := w183_Bgl_cube ω hω
    rwa [pow_succ] at this
  exact inv_eq_of_mul_eq_one_left h

private theorem w183_word_one (ω : K) (hω : ω ^ 2 = ω + 1) :
    w183_Bgl ω * ((w183_Pgl (K := K))⁻¹ * w183_Bgl ω * w183_Pgl (K := K) *
        (w183_Bgl ω)⁻¹) ^ 2 * ((w183_Pgl (K := K))⁻¹ * w183_Bgl ω) ^ 3 *
      w183_Pgl (K := K) * w183_Bgl ω =
      w183_tv 0 1 (by decide) 1 := by
  rw [w183_Pgl_inv, w183_Bgl_inv ω hω]
  apply Units.ext
  rw [show ((w183_Bgl ω * (w183_Pgl (K := K) ^ 2 * w183_Bgl ω * w183_Pgl (K := K) *
        (w183_Bgl ω) ^ 2) ^ 2 * (w183_Pgl (K := K) ^ 2 * w183_Bgl ω) ^ 3 *
        w183_Pgl (K := K) * w183_Bgl ω : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      w183_Bm ω * (w183_Pm ^ 2 * w183_Bm ω * w183_Pm * w183_Bm ω ^ 2) ^ 2 *
        (w183_Pm ^ 2 * w183_Bm ω) ^ 3 * w183_Pm * w183_Bm ω from by
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, w183_Pgl_val, w183_Bgl_val]]
  rw [w183_tv01_val]
  exact w183_word1mat ω hω

private theorem w183_word_omega (ω : K) (hω : ω ^ 2 = ω + 1) :
    w183_Bgl ω * (w183_Pgl (K := K) * (w183_Bgl ω)⁻¹) ^ 2 *
        ((w183_Pgl (K := K))⁻¹ * (w183_Bgl ω)⁻¹ * w183_Pgl (K := K) * w183_Bgl ω) ^ 2 *
        w183_Pgl (K := K) * (w183_Bgl ω)⁻¹ * w183_Pgl (K := K) =
      w183_tv 0 1 (by decide) ω := by
  rw [w183_Pgl_inv, w183_Bgl_inv ω hω]
  apply Units.ext
  rw [show ((w183_Bgl ω * (w183_Pgl (K := K) * (w183_Bgl ω) ^ 2) ^ 2 *
        (w183_Pgl (K := K) ^ 2 * (w183_Bgl ω) ^ 2 * w183_Pgl (K := K) * w183_Bgl ω) ^ 2 *
        w183_Pgl (K := K) * (w183_Bgl ω) ^ 2 * w183_Pgl (K := K) : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) =
      w183_Bm ω * (w183_Pm * w183_Bm ω ^ 2) ^ 2 *
        (w183_Pm ^ 2 * w183_Bm ω ^ 2 * w183_Pm * w183_Bm ω) ^ 2 *
        w183_Pm * w183_Bm ω ^ 2 * w183_Pm from by
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, w183_Pgl_val, w183_Bgl_val]]
  rw [show (w183_tv 0 1 (by decide) ω : Matrix (Fin 3) (Fin 3) K) =
      !![1, ω, 0; 0, 1, 0; 0, 0, 1] from w183_tv01_val ω]
  exact w183_word2mat ω hω

private theorem w183_tv_add (i j : Fin 3) (hij : i ≠ j) (a b : K) :
    w183_tv i j hij a * w183_tv i j hij b = w183_tv i j hij (a + b) := by
  apply Units.ext
  simp only [Units.val_mul, w183_tv_val]
  exact Matrix.transvection_mul_transvection_same i j hij a b

private theorem w183_conj01 (ω : K) (hω : ω ^ 2 = ω + 1) (c : K) :
    w183_Pgl (K := K) * w183_tv 0 1 (by decide) c * (w183_Pgl (K := K))⁻¹ =
      w183_tv 2 0 (by decide) c := by
  rw [w183_Pgl_inv]
  apply Units.ext
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, w183_Pgl_val, w183_tv_val]
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    simp [Matrix.mul_apply, Fin.sum_univ_three, pow_succ, Matrix.one_apply, Matrix.transvection,
      Matrix.single_apply, Matrix.vecMul, dotProduct]
    try ring_nf

private theorem w183_conj20 (ω : K) (hω : ω ^ 2 = ω + 1) (c : K) :
    w183_Pgl (K := K) * w183_tv 2 0 (by decide) c * (w183_Pgl (K := K))⁻¹ =
      w183_tv 1 2 (by decide) c := by
  rw [w183_Pgl_inv]
  apply Units.ext
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, w183_Pgl_val, w183_tv_val]
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    simp [Matrix.mul_apply, Fin.sum_univ_three, pow_succ, Matrix.one_apply, Matrix.transvection,
      Matrix.single_apply, Matrix.vecMul, dotProduct]
    try ring_nf

private theorem w183_comm201 (a b : K) :
    ⁅w183_tv 2 0 (by decide) a, w183_tv 0 1 (by decide) b⁆ =
      w183_tv 2 1 (by decide) (a * b) := by
  rw [w183_tv, w183_tv, w183_tv, ← map_commutatorElement,
    Matrix.SpecialLinearGroup.commutatorElement_transvection]

private theorem w183_comm012 (a b : K) :
    ⁅w183_tv 0 1 (by decide) a, w183_tv 1 2 (by decide) b⁆ =
      w183_tv 0 2 (by decide) (a * b) := by
  rw [w183_tv, w183_tv, w183_tv, ← map_commutatorElement,
    Matrix.SpecialLinearGroup.commutatorElement_transvection]

private theorem w183_comm120 (a b : K) :
    ⁅w183_tv 1 2 (by decide) a, w183_tv 2 0 (by decide) b⁆ =
      w183_tv 1 0 (by decide) (a * b) := by
  rw [w183_tv, w183_tv, w183_tv, ← map_commutatorElement,
    Matrix.SpecialLinearGroup.commutatorElement_transvection]

private noncomputable def w183_P : ↥(StatedSL 3 K) :=
  ⟨w183_Pgl, Subgroup.subset_closure (by simpa [w183_Pgl_val] using w183_Pm_det)⟩

private noncomputable def w183_B (ω : K) : ↥(StatedSL 3 K) :=
  ⟨w183_Bgl ω, Subgroup.subset_closure (by simpa [w183_Bgl_val] using w183_Bm_det ω)⟩

private theorem w183_StatedSL_le (hK : Nat.card K = 4) (ω : K) (hω : ω ^ 2 + ω + 1 = 0) :
    StatedSL 3 K ≤ Subgroup.closure ({w183_Pgl (K := K), w183_Bgl ω} : Set (GL (Fin 3) K)) := by
  have hω' : ω ^ 2 = ω + 1 := by
    have h' : ω ^ 2 + (ω + 1) = 0 := by rwa [add_assoc] at hω
    exact (CharTwo.add_eq_zero).mp h'
  let H : Subgroup (GL (Fin 3) K) := Subgroup.closure {w183_Pgl (K := K), w183_Bgl ω}
  have hP : w183_Pgl (K := K) ∈ H := Subgroup.subset_closure (by simp)
  have hB : w183_Bgl ω ∈ H := Subgroup.subset_closure (by simp)
  have hword1 : w183_tv 0 1 (by decide) 1 ∈ H := by
    rw [← w183_word_one ω hω']
    repeat' first
      | apply H.mul_mem
      | apply H.inv_mem
      | apply H.pow_mem
      | exact hP
      | exact hB
  have hwordomega : w183_tv 0 1 (by decide) ω ∈ H := by
    rw [← w183_word_omega ω hω']
    repeat' first
      | apply H.mul_mem
      | apply H.inv_mem
      | apply H.pow_mem
      | exact hP
      | exact hB
  have htv01 : ∀ c : K, w183_tv 0 1 (by decide) c ∈ H := by
    intro c
    rcases w183_cover_omega (K := K) hK hω c with rfl | rfl | rfl | rfl
    · have h0 : w183_tv 0 1 (by decide) (0 : K) = 1 := by
        apply Units.ext
        simp [w183_tv_val]
      rw [h0]; exact H.one_mem
    · exact hword1
    · exact hwordomega
    · rw [show (ω : K) + 1 = 1 + ω by ring]
      rw [← w183_tv_add]
      exact H.mul_mem hword1 hwordomega
  have htv20 : ∀ c : K, w183_tv 2 0 (by decide) c ∈ H := by
    intro c
    rw [← w183_conj01 ω hω' c]
    exact H.mul_mem (H.mul_mem hP (htv01 c)) (H.inv_mem hP)
  have htv12 : ∀ c : K, w183_tv 1 2 (by decide) c ∈ H := by
    intro c
    rw [← w183_conj20 ω hω' c]
    exact H.mul_mem (H.mul_mem hP (htv20 c)) (H.inv_mem hP)
  have htv21 : ∀ c : K, w183_tv 2 1 (by decide) c ∈ H := by
    intro c
    have h := w183_comm201 (1 : K) c
    rw [one_mul] at h
    rw [← h, commutatorElement_def]
    exact H.mul_mem (H.mul_mem (H.mul_mem (htv20 1) (htv01 c)) (H.inv_mem (htv20 1)))
      (H.inv_mem (htv01 c))
  have htv02 : ∀ c : K, w183_tv 0 2 (by decide) c ∈ H := by
    intro c
    have h := w183_comm012 (1 : K) c
    rw [one_mul] at h
    rw [← h, commutatorElement_def]
    exact H.mul_mem (H.mul_mem (H.mul_mem (htv01 1) (htv12 c)) (H.inv_mem (htv01 1)))
      (H.inv_mem (htv12 c))
  have htv10 : ∀ c : K, w183_tv 1 0 (by decide) c ∈ H := by
    intro c
    have h := w183_comm120 (1 : K) c
    rw [one_mul] at h
    rw [← h, commutatorElement_def]
    exact H.mul_mem (H.mul_mem (H.mul_mem (htv12 1) (htv20 c)) (H.inv_mem (htv12 1)))
      (H.inv_mem (htv20 c))
  have htv : ∀ (i j : Fin 3) (hij : i ≠ j) (c : K), w183_tv i j hij c ∈ H := by
    intro i j hij c
    fin_cases i <;> fin_cases j <;>
      first
        | exact absurd rfl hij
        | exact htv01 c
        | exact htv02 c
        | exact htv10 c
        | exact htv12 c
        | exact htv20 c
        | exact htv21 c
  intro x hx
  rw [CFSG.Open.StatedAPI.statedSL_eq_range_toGL] at hx
  obtain ⟨A, rfl⟩ := hx
  have hgen : ∀ y ∈ CFSG.LinearGroups.elementarySet 3 K,
      SpecialLinearGroup.toGL y ∈ H := by
    rintro y ⟨i, j, hij, c, rfl⟩
    exact htv i j hij c
  have hcl : Subgroup.closure (CFSG.LinearGroups.elementarySet 3 K) ≤
      H.comap (SpecialLinearGroup.toGL :
        SpecialLinearGroup (Fin 3) K →* GL (Fin 3) K) := by
    rw [Subgroup.closure_le]
    exact hgen
  have hA : A ∈ Subgroup.closure (CFSG.LinearGroups.elementarySet 3 K) := by
    rw [CFSG.LinearGroups.special_linear_elementary_generation]
    exact Subgroup.mem_top A
  exact hcl hA

private theorem w183_closure_top (hK : Nat.card K = 4) (ω : K) (hω : ω ^ 2 + ω + 1 = 0) :
    Subgroup.closure ({w183_P (K := K), w183_B ω} : Set ↥(StatedSL 3 K)) = ⊤ := by
  let H : Subgroup ↥(StatedSL 3 K) := Subgroup.closure {w183_P (K := K), w183_B ω}
  have hle : StatedSL 3 K ≤
      Subgroup.closure ({w183_Pgl (K := K), w183_Bgl ω} : Set (GL (Fin 3) K)) :=
    w183_StatedSL_le hK ω hω
  have hmap : H.map (StatedSL 3 K).subtype =
      Subgroup.closure ({w183_Pgl (K := K), w183_Bgl ω} : Set (GL (Fin 3) K)) := by
    change (Subgroup.closure {w183_P (K := K), w183_B ω}).map (StatedSL 3 K).subtype = _
    rw [MonoidHom.map_closure]
    congr 1
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    · intro hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact ⟨w183_P (K := K), by simp, rfl⟩
      · exact ⟨w183_B ω, by simp, rfl⟩
  have hcomap : (Subgroup.closure ({w183_Pgl (K := K), w183_Bgl ω} :
      Set (GL (Fin 3) K))).comap (StatedSL 3 K).subtype = H := by
    rw [← hmap]
    exact Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _) H
  apply eq_top_iff.mpr
  intro g _
  have hg : g ∈ (Subgroup.closure ({w183_Pgl (K := K), w183_Bgl ω} :
      Set (GL (Fin 3) K))).comap (StatedSL 3 K).subtype := hle g.2
  rwa [hcomap] at hg

theorem s16nt_l34_gen {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 4) :
    ∃ (ω : K) (P B : ↥(StatedSL 3 K)), ω ^ 2 + ω + 1 = 0 ∧
      ((P : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = !![0, 1, 0; 0, 0, 1; 1, 0, 0] ∧
      ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = !![1, 1, ω; 0, 1, 1; 0, 1, 0] ∧
      P ^ 3 = 1 ∧ B ^ 3 = 1 ∧ Subgroup.closure {P, B} = ⊤ := by
  obtain ⟨ω, hω⟩ := w183_exists_omega (K := K) hK
  refine ⟨ω, w183_P (K := K), w183_B ω, hω, ?_, ?_, ?_, ?_, ?_⟩
  · change ((w183_Pgl (K := K) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      !![0, 1, 0; 0, 0, 1; 1, 0, 0]
    rw [w183_Pgl_val]
  · change ((w183_Bgl ω : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      !![1, 1, ω; 0, 1, 1; 0, 1, 0]
    rw [w183_Bgl_val]
  · change (w183_P (K := K)) ^ 3 = 1
    apply Subtype.ext
    change (w183_Pgl (K := K)) ^ 3 = (1 : GL (Fin 3) K)
    exact w183_Pgl_cube
  · change (w183_B ω) ^ 3 = 1
    have hω' : ω ^ 2 = ω + 1 := by
      have h' : ω ^ 2 + (ω + 1) = 0 := by rwa [add_assoc] at hω
      exact (CharTwo.add_eq_zero).mp h'
    apply Subtype.ext
    change (w183_Bgl ω) ^ 3 = (1 : GL (Fin 3) K)
    exact w183_Bgl_cube ω hω'
  · exact w183_closure_top hK ω hω

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end

