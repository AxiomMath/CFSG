module

public import CFSG.Open.StatedDefs
public import Mathlib.LinearAlgebra.Matrix.Notation

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Matrix
open scoped CharTwo

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem w183_exists_omega (hK : Nat.card K = 4) : ∃ ω : K, ω ^ 2 + ω + 1 = 0 := by
  haveI : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = 4 := by rw [← Nat.card_eq_fintype_card]; exact hK
  have hex : ∃ x : K, x ≠ 0 ∧ x ≠ 1 := by
    by_contra h
    have h1 : ∀ x : K, x = 0 ∨ x = 1 := by
      intro x
      by_cases hx0 : x = 0
      · exact Or.inl hx0
      · by_cases hx1 : x = 1
        · exact Or.inr hx1
        · exact absurd ⟨x, hx0, hx1⟩ h
    let f : Fin 2 → K := fun i => if i = 0 then 0 else 1
    have hf : Function.Surjective f := by
      intro x
      rcases h1 x with hx | hx
      · exact ⟨0, by simp [f, hx]⟩
      · exact ⟨1, by simp [f, hx]⟩
    have hle : Fintype.card K ≤ Fintype.card (Fin 2) :=
      Fintype.card_le_of_surjective f hf
    simp at hle
    omega
  obtain ⟨x, hx0, hx1⟩ := hex
  refine ⟨x, ?_⟩
  have hx3 : x ^ 3 = 1 := by
    have := FiniteField.pow_card_sub_one_eq_one x hx0
    rw [hcard] at this
    simpa using this
  have hfac : x ^ 3 - 1 = (x - 1) * (x ^ 2 + x + 1) := by ring
  have hzero : (x - 1) * (x ^ 2 + x + 1) = 0 := by rw [← hfac, hx3]; ring
  exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hx1)


theorem w183_cover_omega (hK : Nat.card K = 4) {ω : K} (hω : ω ^ 2 + ω + 1 = 0) :
    ∀ a : K, a = 0 ∨ a = 1 ∨ a = ω ∨ a = ω + 1 := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = 4 := by rw [← Nat.card_eq_fintype_card]; exact hK
  have hω0 : ω ≠ 0 := by intro h; rw [h] at hω; simpa using hω
  have hω1 : ω ≠ 1 := by
    intro h; rw [h] at hω
    have : (1 : K) = 0 := by simpa [CharTwo.add_self_eq_zero] using hω
    exact one_ne_zero this
  have hωω1 : ω ≠ ω + 1 := by
    intro h
    have h' : (0 : K) = 1 := by
      have h2 : ω + 0 = ω + 1 := by simpa using h
      exact add_left_cancel h2
    exact one_ne_zero h'.symm
  have h0ω1 : (0 : K) ≠ ω + 1 := by
    intro h
    have : ω = 1 := by
      have h' := congrArg (fun x => x + 1) h
      simpa [CharTwo.add_self_eq_zero] using h'.symm
    exact hω1 this
  have h1ω1 : (1 : K) ≠ ω + 1 := by
    intro h
    have : ω = 0 := by
      have h' := congrArg (fun x => x + 1) h
      simpa [CharTwo.add_self_eq_zero] using h'.symm
    exact hω0 this
  have hS : ({0, 1, ω, ω + 1} : Finset K).card = Fintype.card K := by
    rw [hcard]
    rw [Finset.card_insert_of_notMem (by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨zero_ne_one, Ne.symm hω0, h0ω1⟩),
        Finset.card_insert_of_notMem (by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨Ne.symm hω1, h1ω1⟩),
        Finset.card_insert_of_notMem (by
          simp only [Finset.mem_singleton]
          exact hωω1),
        Finset.card_singleton]
  have hsuniv : ({0, 1, ω, ω + 1} : Finset K) = Finset.univ :=
    (Finset.card_eq_iff_eq_univ _).mp hS
  intro a
  have : a ∈ ({0, 1, ω, ω + 1} : Finset K) := by rw [hsuniv]; exact Finset.mem_univ a
  simpa using this


abbrev w183_Pm : Matrix (Fin 3) (Fin 3) K := !![0, 1, 0; 0, 0, 1; 1, 0, 0]

abbrev w183_Bm (ω : K) : Matrix (Fin 3) (Fin 3) K := !![1, 1, ω; 0, 1, 1; 0, 1, 0]

theorem w183_Pm_det : (w183_Pm (K := K)).det = 1 := by
  rw [w183_Pm, Matrix.det_fin_three]; simp

theorem w183_Bm_det (ω : K) : (w183_Bm ω).det = 1 := by
  rw [w183_Bm, Matrix.det_fin_three]; simp

theorem w183_Pm_cube : (w183_Pm (K := K)) ^ 3 = 1 := by
  rw [w183_Pm]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, pow_succ, Matrix.one_apply]

theorem w183_Bm_cube (ω : K) (hω : ω ^ 2 = ω + 1) : (w183_Bm ω) ^ 3 = 1 := by
  have hω2 : ω * ω = ω + 1 := by rw [← pow_two, hω]
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    simp [Matrix.mul_apply, Fin.sum_univ_three, pow_succ, Matrix.one_apply, hω, hω2]
    try ring_nf
    try simp only [hω, hω2, pow_succ, one_mul, mul_one]
    try ring_nf
    try simp
    try rfl

private theorem w183_hP2 (ω : K) (hω : ω ^ 2 = ω + 1) :
    w183_Pm ^ 2 = (!![0, 0, 1; 1, 0, 0; 0, 1, 0] : Matrix (Fin 3) (Fin 3) K) := by
  have hω2 : ω * ω = ω + 1 := by rw [← pow_two, hω]
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    simp [Matrix.mul_apply, Fin.sum_univ_three, pow_succ, Matrix.one_apply, hω, hω2]
    try ring_nf
    try simp only [hω, hω2, pow_succ, one_mul, mul_one]
    try ring_nf
    try simp
    try rfl

private theorem w183_hB2 (ω : K) (hω : ω ^ 2 = ω + 1) :
    w183_Bm ω ^ 2 = (!![1, ω, ω + 1; 0, 0, 1; 0, 1, 1] : Matrix (Fin 3) (Fin 3) K) := by
  have hω2 : ω * ω = ω + 1 := by rw [← pow_two, hω]
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    simp [Matrix.mul_apply, Fin.sum_univ_three, pow_succ, Matrix.one_apply, hω, hω2]
    try ring_nf
    try simp only [hω, hω2, pow_succ, one_mul, mul_one]
    try ring_nf
    try simp
    try rfl

private theorem w183_hA1 (ω : K) (hω : ω ^ 2 = ω + 1) :
    w183_Pm ^ 2 * w183_Bm ω * w183_Pm * w183_Bm ω ^ 2 =
      (!![0, 1, 1; ω, ω, 1; 1, ω + 1, ω] : Matrix (Fin 3) (Fin 3) K) := by
  have hω2 : ω * ω = ω + 1 := by rw [← pow_two, hω]
  rw [w183_hP2 ω hω, w183_hB2 ω hω]
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    simp [Matrix.mul_apply, Fin.sum_univ_three, pow_succ, Matrix.one_apply, hω, hω2]
    try ring_nf
    try simp only [hω, hω2, pow_succ, one_mul, mul_one]
    try ring_nf
    try simp
    try rfl

private theorem w183_hA1s (ω : K) (hω : ω ^ 2 = ω + 1) :
    (!![0, 1, 1; ω, ω, 1; 1, ω + 1, ω] : Matrix (Fin 3) (Fin 3) K) *
        !![0, 1, 1; ω, ω, 1; 1, ω + 1, ω] =
      (!![ω + 1, 1, ω + 1; ω, ω, ω; ω + 1, 1, 1] : Matrix (Fin 3) (Fin 3) K) := by
  have hω2 : ω * ω = ω + 1 := by rw [← pow_two, hω]
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    simp [Matrix.mul_apply, Fin.sum_univ_three, pow_succ, Matrix.one_apply, hω, hω2]
    try ring_nf
    try simp only [hω, hω2, pow_succ, one_mul, mul_one]
    try ring_nf
    try simp
    try rfl

private theorem w183_hA3 (ω : K) (hω : ω ^ 2 = ω + 1) :
    w183_Pm ^ 2 * w183_Bm ω = (!![0, 1, 0; 1, 1, ω; 0, 1, 1] : Matrix (Fin 3) (Fin 3) K) := by
  have hω2 : ω * ω = ω + 1 := by rw [← pow_two, hω]
  rw [w183_hP2 ω hω]
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    simp [Matrix.mul_apply, Fin.sum_univ_three, pow_succ, Matrix.one_apply, hω, hω2]
    try ring_nf
    try simp only [hω, hω2, pow_succ, one_mul, mul_one]
    try ring_nf
    try simp
    try rfl

private theorem w183_hA3c (ω : K) (hω : ω ^ 2 = ω + 1) :
    (!![0, 1, 0; 1, 1, ω; 0, 1, 1] : Matrix (Fin 3) (Fin 3) K) *
        !![0, 1, 0; 1, 1, ω; 0, 1, 1] * !![0, 1, 0; 1, 1, ω; 0, 1, 1] =
      (!![1, ω, 0; ω, ω + 1, ω + 1; 0, ω, ω + 1] : Matrix (Fin 3) (Fin 3) K) := by
  have hω2 : ω * ω = ω + 1 := by rw [← pow_two, hω]
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    simp [Matrix.mul_apply, Fin.sum_univ_three, pow_succ, Matrix.one_apply, hω, hω2]
    try ring_nf
    try simp only [hω, hω2, pow_succ, one_mul, mul_one]
    try ring_nf
    try simp
    try rfl

private theorem w183_hE1 (ω : K) (hω : ω ^ 2 = ω + 1) :
    w183_Bm ω * (!![ω + 1, 1, ω + 1; ω, ω, ω; ω + 1, 1, 1] : Matrix (Fin 3) (Fin 3) K) =
      (!![0, 1, ω + 1; 1, ω + 1, ω + 1; ω, ω, ω] : Matrix (Fin 3) (Fin 3) K) := by
  have hω2 : ω * ω = ω + 1 := by rw [← pow_two, hω]
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    simp [Matrix.mul_apply, Fin.sum_univ_three, pow_succ, Matrix.one_apply, hω, hω2]
    try ring_nf
    try simp only [hω, hω2, pow_succ, one_mul, mul_one]
    try ring_nf
    try simp
    try rfl

private theorem w183_hE2 (ω : K) (hω : ω ^ 2 = ω + 1) :
    (!![0, 1, ω + 1; 1, ω + 1, ω + 1; ω, ω, ω] : Matrix (Fin 3) (Fin 3) K) *
        !![1, ω, 0; ω, ω + 1, ω + 1; 0, ω, ω + 1] =
      (!![ω, ω, 1; 0, 1, 0; 1, 1, 0] : Matrix (Fin 3) (Fin 3) K) := by
  have hω2 : ω * ω = ω + 1 := by rw [← pow_two, hω]
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    simp [Matrix.mul_apply, Fin.sum_univ_three, pow_succ, Matrix.one_apply, hω, hω2]
    try ring_nf
    try simp only [hω, hω2, pow_succ, one_mul, mul_one]
    try ring_nf
    try simp
    try rfl

private theorem w183_hE3 (ω : K) (hω : ω ^ 2 = ω + 1) :
    (!![ω, ω, 1; 0, 1, 0; 1, 1, 0] : Matrix (Fin 3) (Fin 3) K) * w183_Pm =
      (!![1, ω, ω; 0, 0, 1; 0, 1, 1] : Matrix (Fin 3) (Fin 3) K) := by
  have hω2 : ω * ω = ω + 1 := by rw [← pow_two, hω]
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    simp [Matrix.mul_apply, Fin.sum_univ_three, pow_succ, Matrix.one_apply, hω, hω2]
    try ring_nf
    try simp only [hω, hω2, pow_succ, one_mul, mul_one]
    try ring_nf
    try simp
    try rfl

private theorem w183_hE4 (ω : K) (hω : ω ^ 2 = ω + 1) :
    (!![1, ω, ω; 0, 0, 1; 0, 1, 1] : Matrix (Fin 3) (Fin 3) K) * w183_Bm ω =
      (!![1, 1, 0; 0, 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) K) := by
  have hω2 : ω * ω = ω + 1 := by rw [← pow_two, hω]
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    simp [Matrix.mul_apply, Fin.sum_univ_three, pow_succ, Matrix.one_apply, hω, hω2]
    try ring_nf
    try simp only [hω, hω2, pow_succ, one_mul, mul_one]
    try ring_nf
    try simp
    try rfl

theorem w183_word1mat (ω : K) (hω : ω ^ 2 = ω + 1) :
    w183_Bm ω * (w183_Pm ^ 2 * w183_Bm ω * w183_Pm * w183_Bm ω ^ 2) ^ 2 *
        (w183_Pm ^ 2 * w183_Bm ω) ^ 3 * w183_Pm * w183_Bm ω =
      (!![1, 1, 0; 0, 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) K) := by
  rw [w183_hA1 ω hω, pow_two, w183_hA1s ω hω, w183_hA3 ω hω]
  rw [show (!![0, 1, 0; 1, 1, ω; 0, 1, 1] : Matrix (Fin 3) (Fin 3) K) ^ 3 =
      !![0, 1, 0; 1, 1, ω; 0, 1, 1] * !![0, 1, 0; 1, 1, ω; 0, 1, 1] *
        !![0, 1, 0; 1, 1, ω; 0, 1, 1] by rw [pow_succ, pow_two]]
  rw [w183_hA3c ω hω, w183_hE1 ω hω, w183_hE2 ω hω, w183_hE3 ω hω, w183_hE4 ω hω]

private theorem w183_hC1 (ω : K) (hω : ω ^ 2 = ω + 1) :
    w183_Pm * w183_Bm ω ^ 2 = (!![0, 0, 1; 0, 1, 1; 1, ω, ω + 1] : Matrix (Fin 3) (Fin 3) K) := by
  have hω2 : ω * ω = ω + 1 := by rw [← pow_two, hω]
  rw [w183_hB2 ω hω]
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    simp [Matrix.mul_apply, Fin.sum_univ_three, pow_succ, Matrix.one_apply, hω, hω2]
    try ring_nf
    try simp only [hω, hω2, pow_succ, one_mul, mul_one]
    try ring_nf
    try simp
    try rfl

private theorem w183_hC1s (ω : K) (hω : ω ^ 2 = ω + 1) :
    (!![0, 0, 1; 0, 1, 1; 1, ω, ω + 1] : Matrix (Fin 3) (Fin 3) K) *
        !![0, 0, 1; 0, 1, 1; 1, ω, ω + 1] =
      (!![1, ω, ω + 1; 1, ω + 1, ω; ω + 1, ω + 1, 1] : Matrix (Fin 3) (Fin 3) K) := by
  have hω2 : ω * ω = ω + 1 := by rw [← pow_two, hω]
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    simp [Matrix.mul_apply, Fin.sum_univ_three, pow_succ, Matrix.one_apply, hω, hω2]
    try ring_nf
    try simp only [hω, hω2, pow_succ, one_mul, mul_one]
    try ring_nf
    try simp
    try rfl

private theorem w183_hD1 (ω : K) (hω : ω ^ 2 = ω + 1) :
    w183_Pm ^ 2 * w183_Bm ω ^ 2 * w183_Pm * w183_Bm ω =
      (!![1, 0, ω; ω + 1, 0, 0; 1, 1, ω] : Matrix (Fin 3) (Fin 3) K) := by
  have hω2 : ω * ω = ω + 1 := by rw [← pow_two, hω]
  rw [w183_hP2 ω hω, w183_hB2 ω hω]
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    simp [Matrix.mul_apply, Fin.sum_univ_three, pow_succ, Matrix.one_apply, hω, hω2]
    try ring_nf
    try simp only [hω, hω2, pow_succ, one_mul, mul_one]
    try ring_nf
    try simp
    try rfl

private theorem w183_hD1s (ω : K) (hω : ω ^ 2 = ω + 1) :
    (!![1, 0, ω; ω + 1, 0, 0; 1, 1, ω] : Matrix (Fin 3) (Fin 3) K) *
        !![1, 0, ω; ω + 1, 0, 0; 1, 1, ω] =
      (!![ω + 1, ω, 1; ω + 1, 0, 1; 0, ω, 1] : Matrix (Fin 3) (Fin 3) K) := by
  have hω2 : ω * ω = ω + 1 := by rw [← pow_two, hω]
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    simp [Matrix.mul_apply, Fin.sum_univ_three, pow_succ, Matrix.one_apply, hω, hω2]
    try ring_nf
    try simp only [hω, hω2, pow_succ, one_mul, mul_one]
    try ring_nf
    try simp
    try rfl

private theorem w183_hF1 (ω : K) (hω : ω ^ 2 = ω + 1) :
    w183_Bm ω * (!![1, ω, ω + 1; 1, ω + 1, ω; ω + 1, ω + 1, 1] : Matrix (Fin 3) (Fin 3) K) =
      (!![1, 0, ω + 1; ω, 0, ω + 1; 1, ω + 1, ω] : Matrix (Fin 3) (Fin 3) K) := by
  have hω2 : ω * ω = ω + 1 := by rw [← pow_two, hω]
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    simp [Matrix.mul_apply, Fin.sum_univ_three, pow_succ, Matrix.one_apply, hω, hω2]
    try ring_nf
    try simp only [hω, hω2, pow_succ, one_mul, mul_one]
    try ring_nf
    try simp
    try rfl

private theorem w183_hF2 (ω : K) (hω : ω ^ 2 = ω + 1) :
    (!![1, 0, ω + 1; ω, 0, ω + 1; 1, ω + 1, ω] : Matrix (Fin 3) (Fin 3) K) *
        !![ω + 1, ω, 1; ω + 1, 0, 1; 0, ω, 1] =
      (!![ω + 1, ω + 1, ω; 1, ω, 1; 1, 1, 0] : Matrix (Fin 3) (Fin 3) K) := by
  have hω2 : ω * ω = ω + 1 := by rw [← pow_two, hω]
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    simp [Matrix.mul_apply, Fin.sum_univ_three, pow_succ, Matrix.one_apply, hω, hω2]
    try ring_nf
    try simp only [hω, hω2, pow_succ, one_mul, mul_one]
    try ring_nf
    try simp
    try rfl

private theorem w183_hF3 (ω : K) (hω : ω ^ 2 = ω + 1) :
    (!![ω + 1, ω + 1, ω; 1, ω, 1; 1, 1, 0] : Matrix (Fin 3) (Fin 3) K) * w183_Pm =
      (!![ω, ω + 1, ω + 1; 1, 1, ω; 0, 1, 1] : Matrix (Fin 3) (Fin 3) K) := by
  have hω2 : ω * ω = ω + 1 := by rw [← pow_two, hω]
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    simp [Matrix.mul_apply, Fin.sum_univ_three, pow_succ, Matrix.one_apply, hω, hω2]
    try ring_nf
    try simp only [hω, hω2, pow_succ, one_mul, mul_one]
    try ring_nf
    try simp
    try rfl

private theorem w183_hF4 (ω : K) (hω : ω ^ 2 = ω + 1) :
    (!![ω, ω + 1, ω + 1; 1, 1, ω; 0, 1, 1] : Matrix (Fin 3) (Fin 3) K) * w183_Bm ω ^ 2 =
      (!![ω, 0, 1; 1, 0, 0; 0, 1, 0] : Matrix (Fin 3) (Fin 3) K) := by
  have hω2 : ω * ω = ω + 1 := by rw [← pow_two, hω]
  rw [w183_hB2 ω hω]
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    simp [Matrix.mul_apply, Fin.sum_univ_three, pow_succ, Matrix.one_apply, hω, hω2]
    try ring_nf
    try simp only [hω, hω2, pow_succ, one_mul, mul_one]
    try ring_nf
    try simp
    try rfl

private theorem w183_hF5 (ω : K) (hω : ω ^ 2 = ω + 1) :
    (!![ω, 0, 1; 1, 0, 0; 0, 1, 0] : Matrix (Fin 3) (Fin 3) K) * w183_Pm =
      (!![1, ω, 0; 0, 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) K) := by
  have hω2 : ω * ω = ω + 1 := by rw [← pow_two, hω]
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    simp [Matrix.mul_apply, Fin.sum_univ_three, pow_succ, Matrix.one_apply, hω, hω2]
    try ring_nf
    try simp only [hω, hω2, pow_succ, one_mul, mul_one]
    try ring_nf
    try simp
    try rfl

theorem w183_word2mat (ω : K) (hω : ω ^ 2 = ω + 1) :
    w183_Bm ω * (w183_Pm * w183_Bm ω ^ 2) ^ 2 *
        (w183_Pm ^ 2 * w183_Bm ω ^ 2 * w183_Pm * w183_Bm ω) ^ 2 *
        w183_Pm * w183_Bm ω ^ 2 * w183_Pm =
      (!![1, ω, 0; 0, 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) K) := by
  rw [w183_hC1 ω hω, pow_two, w183_hC1s ω hω, w183_hD1 ω hω, pow_two, w183_hD1s ω hω]
  rw [w183_hF1 ω hω, w183_hF2 ω hω, w183_hF3 ω hω, w183_hF4 ω hω, w183_hF5 ω hω]



end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
