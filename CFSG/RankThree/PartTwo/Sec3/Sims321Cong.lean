module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.RankThree.PartTwo.Sec3.Sims321

open Matrix

variable {F : Type*} [Field F] [Finite F] [CharP F 2]

private theorem alternating_mul_eq (G : Fin 3 → Fin 3 → F) (hs : ∀ i j, G i j = G j i)
    (hd : ∀ i, G i i = 0) (i j r r' : Fin 3) :
    G i j * G r r' = G r i * G r' j + G r j * G r' i := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have h10 := hs 1 0
  have h20 := hs 2 0
  have h21 := hs 2 1
  have h0 := hd 0
  have h1 := hd 1
  have h2' := hd 2
  fin_cases i <;> fin_cases j <;> fin_cases r <;> fin_cases r' <;>
    simp [h10, h20, h21, h0, h1, h2'] <;> ring_nf <;> simp [h2]

private theorem exists_mul_transpose_eq (B : Matrix (Fin 3) (Fin 3) F) (hB : Bᵀ = B)
    (hdet : IsUnit B.det) : ∃ M : Matrix (Fin 3) (Fin 3) F, M * Mᵀ = B := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hsym : ∀ i j, B i j = B j i := fun i j => by
    simpa using (congrFun (congrFun hB i) j).symm
  choose α hα using fun i => isSquare_of_charTwo' (B i i)
  obtain ⟨G, hG⟩ : ∃ G : Fin 3 → Fin 3 → F, ∀ i j, G i j = B i j - α i * α j :=
    ⟨_, fun _ _ => rfl⟩
  have hGs : ∀ i j, G i j = G j i := fun i j => by
    rw [hG, hG, hsym i j, mul_comm (α i)]
  have hGd : ∀ i, G i i = 0 := fun i => by rw [hG, hα i, sub_self]
  obtain ⟨i, j, hij⟩ : ∃ i j, G i j ≠ 0 := by
    by_contra h
    have h0 : ∀ i j, G i j = 0 := fun i j => by_contra fun hne => h ⟨i, j, hne⟩
    have hBe : B = vecMulVec α α := by
      ext i j
      have := h0 i j
      rw [hG, sub_eq_zero] at this
      simpa [vecMulVec_apply] using this
    rw [hBe, det_vecMulVec] at hdet
    exact not_isUnit_zero hdet
  obtain ⟨x, hx⟩ : ∃ x : Fin 3 → F, ∀ r, x r = G r i := ⟨fun r => G r i, fun _ => rfl⟩
  obtain ⟨y, hy⟩ : ∃ y : Fin 3 → F, ∀ r, y r = G r j / G i j :=
    ⟨fun r => G r j / G i j, fun _ => rfl⟩
  refine ⟨Matrix.of fun r c => (![α + x, α + y, α + x + y] : Fin 3 → Fin 3 → F) c r, ?_⟩
  ext r r'
  simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply, Matrix.of_apply]
  simp
  have hp := alternating_mul_eq G hGs hGd i j r r'
  have hG' : G r r' = x r * y r' + y r * x r' := by
    rw [hx, hx, hy, hy]
    field_simp
    linear_combination hp
  have hB' : B r r' = G r r' + α r * α r' := by rw [hG]; ring
  rw [hB']
  linear_combination
    (α r * α r' + α r * (x r' + y r') + α r' * (x r + y r) + x r * x r' + y r * y r') * h2 - hG'

theorem exists_mul_transpose_eq_of_symm (B : GL (Fin 3) F)
    (hB : (B : Matrix (Fin 3) (Fin 3) F)ᵀ = B) :
    ∃ K : GL (Fin 3) F,
      (K : Matrix (Fin 3) (Fin 3) F) * (K : Matrix (Fin 3) (Fin 3) F)ᵀ = B := by
  obtain ⟨M, hM⟩ := exists_mul_transpose_eq (B : Matrix (Fin 3) (Fin 3) F) hB
    (isUnits_det_units B)
  have hu : IsUnit M.det := by
    have h := congrArg Matrix.det hM
    rw [det_mul, det_transpose] at h
    exact isUnit_of_mul_isUnit_left (h ▸ isUnits_det_units B)
  exact ⟨GeneralLinearGroup.mk'' M hu, by simpa using hM⟩

end CFSG.RankThree.PartTwo.Sec3.Sims321
