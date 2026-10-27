module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import CFSG.Open.StatedCenterThree

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item224KFactsProof.SL3Mat

open Matrix

variable {K : Type*} [Field K]

theorem exists_scalar_of_commute {M : Matrix (Fin 3) (Fin 3) K}
    (h : ∀ g : SpecialLinearGroup (Fin 3) K, M * (g : Matrix (Fin 3) (Fin 3) K) = g * M) :
    ∃ c : K, M = scalar (Fin 3) c := by
  have hM : M ∈ Set.range (scalar (Fin 3) : K →+* Matrix (Fin 3) (Fin 3) K) := by
    rw [Matrix.mem_range_scalar_iff_commute_transvectionStruct]
    intro t
    exact (h ⟨t.toMatrix, t.det⟩).symm
  obtain ⟨c, hc⟩ := hM
  exact ⟨c, hc.symm⟩

theorem eq_diagonal_of_commute {d : Fin 3 → K} (hd : Function.Injective d)
    {M : Matrix (Fin 3) (Fin 3) K} (h : M * diagonal d = diagonal d * M) :
    M = diagonal fun i => M i i :=
  CFSG.Open.StatedCenterThree.eq_diagonal_of_commute hd h

theorem cube_eq_one_of_sq_add {ζ : K} (hζ : ζ ^ 2 + ζ + 1 = 0) : ζ ^ 3 = 1 := by
  linear_combination (ζ - 1) * hζ

theorem cube_root_cases {ζ r : K} (hζ : ζ ^ 2 + ζ + 1 = 0) (hr : r ^ 3 = 1) :
    r = 1 ∨ r = ζ ∨ r = ζ ^ 2 := by
  have h3 := cube_eq_one_of_sq_add hζ
  have h : (r - 1) * (r - ζ) * (r - ζ ^ 2) = 0 := by
    linear_combination hr - r ^ 2 * hζ + r * hζ + r * h3 - h3
  rcases mul_eq_zero.mp h with h | h
  · rcases mul_eq_zero.mp h with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (Or.inl (sub_eq_zero.mp h))
  · exact Or.inr (Or.inr (sub_eq_zero.mp h))

theorem sq_eq_sq_char_two [CharP K 2] {a b : K} (h : a ^ 2 = b ^ 2) : a = b := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply frobenius_inj K 2
  rw [frobenius_def, frobenius_def, h]

theorem eq_one_of_sq_eq_one [CharP K 2] {a : K} (h : a ^ 2 = 1) : a = 1 :=
  sq_eq_sq_char_two (h.trans (one_pow 2).symm)

@[expose] def cycMat : Matrix (Fin 3) (Fin 3) K := !![0, 0, 1; 1, 0, 0; 0, 1, 0]

@[expose] def cycInvMat : Matrix (Fin 3) (Fin 3) K := !![0, 1, 0; 0, 0, 1; 1, 0, 0]

theorem cycMat_mul_cycInvMat : (cycMat : Matrix (Fin 3) (Fin 3) K) * cycInvMat = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cycMat, cycInvMat, Matrix.mul_apply, Fin.sum_univ_three]

theorem det_cycMat : (cycMat : Matrix (Fin 3) (Fin 3) K).det = 1 := by
  simp [cycMat, det_fin_three]

@[expose] def cyc : SpecialLinearGroup (Fin 3) K := ⟨cycMat, det_cycMat⟩

theorem cyc_coe : ((cyc : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = cycMat :=
  rfl

theorem cyc_inv_coe :
    ((cyc⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = cycInvMat := by
  have h : (cyc : SpecialLinearGroup (Fin 3) K) * ⟨cycInvMat, by
      simp [cycInvMat, det_fin_three]⟩ = 1 :=
    Subtype.ext (by
      change (cycMat : Matrix (Fin 3) (Fin 3) K) * cycInvMat = 1
      exact cycMat_mul_cycInvMat)
  rw [inv_eq_of_mul_eq_one_right h]

theorem cycInvMat_transpose : (cycInvMat : Matrix (Fin 3) (Fin 3) K)ᵀ = cycMat := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cycMat, cycInvMat]

theorem cycMat_mul_diagonal (a b c : K) :
    (cycMat : Matrix (Fin 3) (Fin 3) K) * diagonal ![a, b, c] = diagonal ![c, a, b] * cycMat := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cycMat, Matrix.mul_apply, diagonal_apply]

theorem cycMat_mulVec_single (i : Fin 3) (r : K) :
    (cycMat : Matrix (Fin 3) (Fin 3) K) *ᵥ Pi.single i r = Pi.single (i + 1) r := by
  ext k
  fin_cases i <;> fin_cases k <;> simp [cycMat, mulVec, dotProduct, Fin.sum_univ_three]

theorem eq_scalar_of_diagonal_commute_cyc {d : Fin 3 → K}
    (h : diagonal d * cycMat = cycMat * diagonal d) : d 0 = d 1 ∧ d 1 = d 2 := by
  have e10 := congrFun (congrFun h 1) 0
  have e21 := congrFun (congrFun h 2) 1
  simp [cycMat, Matrix.mul_apply, diagonal_apply] at e10 e21
  exact ⟨e10.symm, e21.symm⟩

theorem mem_center_iff_scalar {z : SpecialLinearGroup (Fin 3) K} :
    z ∈ Subgroup.center (SpecialLinearGroup (Fin 3) K) ↔
      ∃ r : K, r ^ 3 = 1 ∧ (z : Matrix (Fin 3) (Fin 3) K) = scalar (Fin 3) r := by
  rw [Matrix.SpecialLinearGroup.mem_center_iff, Fintype.card_fin]
  exact ⟨fun ⟨r, hr, h⟩ => ⟨r, hr, h.symm⟩, fun ⟨r, hr, h⟩ => ⟨r, hr, h.symm⟩⟩

@[expose] def scalarSL (r : K) (hr : r ^ 3 = 1) : SpecialLinearGroup (Fin 3) K :=
  ⟨scalar (Fin 3) r, by
    rw [scalar_apply, det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin, hr]⟩

theorem scalarSL_coe (r : K) (hr : r ^ 3 = 1) :
    ((scalarSL r hr : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      scalar (Fin 3) r :=
  rfl

theorem scalarSL_mem_center (r : K) (hr : r ^ 3 = 1) :
    scalarSL r hr ∈ Subgroup.center (SpecialLinearGroup (Fin 3) K) :=
  mem_center_iff_scalar.mpr ⟨r, hr, rfl⟩

theorem pow_three_of_mem_center {z : SpecialLinearGroup (Fin 3) K}
    (hz : z ∈ Subgroup.center (SpecialLinearGroup (Fin 3) K)) : z ^ 3 = 1 := by
  obtain ⟨r, hr, h⟩ := mem_center_iff_scalar.mp hz
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, h, ← map_pow, hr, map_one]
  rfl

theorem eq_one_of_diagonal_sq [CharP K 2] {g : SpecialLinearGroup (Fin 3) K}
    (hg : (g : Matrix (Fin 3) (Fin 3) K) = diagonal fun i => g i i) (h2 : g ^ 2 = 1) : g = 1 := by
  have hm := congrArg (fun h : SpecialLinearGroup (Fin 3) K => (h : Matrix (Fin 3) (Fin 3) K)) h2
  simp only [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one] at hm
  rw [hg, diagonal_pow] at hm
  have hi : ∀ i : Fin 3, g i i = 1 := fun i => by
    have := congrFun (congrFun hm i) i
    rw [diagonal_apply_eq, one_apply_eq] at this
    exact eq_one_of_sq_eq_one this
  apply Subtype.ext
  rw [hg, Matrix.SpecialLinearGroup.coe_one]
  ext i j
  by_cases hij : i = j
  · subst hij
    rw [diagonal_apply_eq, hi, one_apply_eq]
  · rw [diagonal_apply_ne _ hij, one_apply_ne hij]

end CFSG.RankThree.PartTwo.Sec21.Item224KFactsProof.SL3Mat
