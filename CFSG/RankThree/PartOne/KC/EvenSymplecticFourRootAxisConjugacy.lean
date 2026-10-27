module

public import CFSG.RankThree.PartOne.KC.EvenSymplecticFourRootAxisDefs

public section

namespace CFSG.RankThree.PartOne

namespace KCRootAxis

open Matrix CFSG.ComponentClassification.UnbalancedCatalog.SpChain
  CFSG.QuasithinUnique.Setup.X7b

variable {K : Type} [Field K] [CharP K 2]

theorem not_conj_radA2_le_radA1 (g : antiSp K)
    (h : ∀ y ∈ radA2 K, g * y * g⁻¹ ∈ radA1 K) : False := by
  have hZ : ∀ z ∈ radA2 K, ∃ b c d : K, z * g⁻¹ = g⁻¹ * uElt 0 b c d := by
    intro z hz
    obtain ⟨b, c, d, hy⟩ := h z hz
    refine ⟨b, c, d, ?_⟩
    calc z * g⁻¹ = g⁻¹ * (g * z * g⁻¹) := by group
      _ = g⁻¹ * uElt 0 b c d := by rw [hy]
  obtain ⟨b1, c1, d1, h1⟩ := hZ (uElt 1 0 0 0) ⟨1, 0, 0, rfl⟩
  obtain ⟨b2, c2, d2, h2⟩ := hZ (uElt 0 1 0 0) ⟨0, 1, 0, rfl⟩
  have e1 := congrArg mat h1
  have e2 := congrArg mat h2
  rw [mat_mul, mat_mul] at e1 e2
  have hPQ : mat g * mat g⁻¹ = 1 := by
    rw [← mat_mul, mul_inv_cancel, mat_one]
  obtain ⟨Q, hQ⟩ : ∃ Q : Matrix (Fin 4) (Fin 4) K, Q = mat g⁻¹ := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : Matrix (Fin 4) (Fin 4) K, P = mat g := ⟨_, rfl⟩
  rw [← hQ] at e1 e2 hPQ
  rw [← hP] at hPQ
  have q10 : Q 1 0 = 0 := by
    have := congrFun (congrFun e1 0) 0
    simp [Matrix.mul_apply, Fin.sum_univ_four, mat, glMat_uElt, uMat] at this
    exact this
  have q30 : Q 3 0 = 0 := by
    have := congrFun (congrFun e1 2) 0
    simp [Matrix.mul_apply, Fin.sum_univ_four, mat, glMat_uElt, uMat] at this
    exact this
  have q11 : Q 1 1 = 0 := by
    have := congrFun (congrFun e1 0) 1
    simp [Matrix.mul_apply, Fin.sum_univ_four, mat, glMat_uElt, uMat] at this
    exact this
  have q31 : Q 3 1 = 0 := by
    have := congrFun (congrFun e1 2) 1
    simp [Matrix.mul_apply, Fin.sum_univ_four, mat, glMat_uElt, uMat] at this
    exact this
  have q20 : Q 2 0 = 0 := by
    have := congrFun (congrFun e2 0) 0
    simp [Matrix.mul_apply, Fin.sum_univ_four, mat, glMat_uElt, uMat] at this
    exact this
  have q21 : Q 2 1 = 0 := by
    have := congrFun (congrFun e2 0) 1
    simp [Matrix.mul_apply, Fin.sum_univ_four, mat, glMat_uElt, uMat] at this
    exact this
  have a00 := congrFun (congrFun hPQ 0) 0
  have a10 := congrFun (congrFun hPQ 1) 0
  have a11 := congrFun (congrFun hPQ 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_four, q10, q20, q30, q11, q21, q31] at a00 a10 a11
  have hne : Q 0 0 ≠ 0 := fun h0 => by
    rw [h0] at a00
    simp at a00
  have hg10 : P 1 0 = 0 := a10.resolve_right hne
  rw [hg10] at a11
  simp at a11

theorem radA2_not_conj_radA1 (g : antiSp K) :
    ¬ ∀ z : antiSp K, z ∈ radA2 K ↔ g * z * g⁻¹ ∈ radA1 K := fun h =>
  not_conj_radA2_le_radA1 g fun y hy => (h y).mp hy

end KCRootAxis

end CFSG.RankThree.PartOne
