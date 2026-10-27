module

public import CFSG.Quasithin.AppendixH.H9.H92.OrthoBasis.OrthonormalBasis
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.Matrix.DotProduct

public section

open scoped Matrix

namespace CFSG.ASVolI.ChH

private theorem exists_fixedPoint_of_mul_self_eq_one {n : ℕ} (hn : Odd n)
    (σ : Equiv.Perm (Fin n)) (h : σ * σ = 1) : ∃ i, σ i = i := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : σ ^ 2 ^ 1 = 1 := by rw [pow_one, pow_two]; exact h
  have hmod := Equiv.Perm.card_compl_support_modEq h2
  rw [Fintype.card_fin] at hmod
  by_contra hne
  have hsupp : σ.supportᶜ = ∅ := by
    ext i
    simp only [Finset.mem_compl, Equiv.Perm.mem_support, not_not, Finset.notMem_empty, iff_false]
    exact fun hi => hne ⟨i, hi⟩
  rw [hsupp, Finset.card_empty] at hmod
  obtain ⟨m, rfl⟩ := hn
  unfold Nat.ModEq at hmod
  omega

private theorem det_eq_zero_of_symm_of_diag_zero {n : ℕ} (hn : Odd n)
    {S : Matrix (Fin n) (Fin n) (ZMod 2)} (hS : Sᵀ = S) (hd : ∀ i, S i i = 0) : S.det = 0 := by
  rw [Matrix.det_apply]
  have hsymm : ∀ i j, S i j = S j i := fun i j => by
    have := congrFun (congrFun hS j) i
    simpa [Matrix.transpose_apply] using this
  refine Finset.sum_ninvolution (fun σ => σ⁻¹) ?_ ?_ (fun _ => Finset.mem_univ _)
    (fun σ => inv_inv σ)
  · intro σ
    have hprod : ∏ i, S (σ⁻¹ i) i = ∏ i, S (σ i) i := by
      rw [← Equiv.prod_comp σ (fun i => S (σ⁻¹ i) i)]
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [show σ⁻¹ (σ j) = j from σ.symm_apply_apply j]
      exact hsymm _ _
    rw [Equiv.Perm.sign_inv, hprod]
    exact CharTwo.add_self_eq_zero _
  · intro σ hσ hinv
    have hprod : ∏ i, S (σ i) i ≠ 0 := fun h0 => hσ (by rw [h0, smul_zero])
    have hne : ∀ i, σ i ≠ i := fun i hi => by
      have := Finset.prod_ne_zero_iff.mp hprod i (Finset.mem_univ i)
      rw [hi, hd i] at this
      exact this rfl
    have hmul : σ * σ = 1 := by
      calc σ * σ = σ⁻¹ * σ := by rw [hinv]
        _ = 1 := inv_mul_cancel σ
    obtain ⟨i, hi⟩ := exists_fixedPoint_of_mul_self_eq_one hn σ hmul
    exact hne i hi

theorem exists_mul_mul_transpose_eq_one {n : ℕ} (hn : Odd n) {S : Matrix (Fin n) (Fin n) (ZMod 2)}
    (hS : Sᵀ = S) (hdet : IsUnit S.det) :
    ∃ R : Matrix (Fin n) (Fin n) (ZMod 2), R * S * Rᵀ = 1 := by
  have hdiag : ∃ i, S i i = 1 := by
    by_contra hcon
    refine hdet.ne_zero (det_eq_zero_of_symm_of_diag_zero hn hS fun i => ?_)
    have hz : ∀ c : ZMod 2, c ≠ 1 → c = 0 := by decide
    exact hz _ fun h => hcon ⟨i, h⟩
  obtain ⟨i₀, hi₀⟩ := hdiag
  have hvm : ∀ x : Fin n → ZMod 2, x ᵥ* S = S *ᵥ x := fun x => by
    rw [← Matrix.vecMul_transpose, hS]
  have hsymm : ∀ x y, Matrix.toBilin' S x y = Matrix.toBilin' S y x := by
    intro x y
    rw [Matrix.toBilin'_apply', Matrix.toBilin'_apply', Matrix.dotProduct_mulVec, hvm,
      dotProduct_comm]
  have hnd : ∀ w, (∀ w', Matrix.toBilin' S w w' = 0) → w = 0 := by
    intro w hw
    have h1 : S *ᵥ w = 0 := by
      refine dotProduct_eq_zero _ fun w' => ?_
      rw [← hvm, ← Matrix.dotProduct_mulVec]
      simpa [Matrix.toBilin'_apply'] using hw w'
    have h2 : w = S⁻¹ *ᵥ (S *ᵥ w) := by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul S hdet, Matrix.one_mulVec]
    rw [h2, h1, Matrix.mulVec_zero]
  have hna : ∃ x, Matrix.toBilin' S x x = 1 :=
    ⟨Pi.single i₀ 1, by rw [Matrix.toBilin'_single]; exact hi₀⟩
  obtain ⟨e, he⟩ := exists_orthonormal_family_of_nondegenerate (Matrix.toBilin' S) hsymm hnd hna
    (Module.finrank_fin_fun (ZMod 2))
  refine ⟨Matrix.of e, ?_⟩
  ext i j
  have h1 := he i j
  rw [Matrix.toBilin'_apply'] at h1
  rw [Matrix.one_apply, ← h1]
  simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.transpose_apply, dotProduct, Matrix.mulVec,
    Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

theorem exists_unit_mul_transpose_eq {n : ℕ} (hn : Odd n) (A : GL (Fin n) (ZMod 2))
    (hA : (A : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ = A) :
    ∃ B : GL (Fin n) (ZMod 2),
      (B : Matrix (Fin n) (Fin n) (ZMod 2)) * (B : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ = A := by
  obtain ⟨R, hR⟩ := exists_mul_mul_transpose_eq_one hn hA
    ((Matrix.isUnit_iff_isUnit_det _).mp A.isUnit)
  have h1 : R * ((A : Matrix (Fin n) (Fin n) (ZMod 2)) * Rᵀ) = 1 := by
    rw [← Matrix.mul_assoc]; exact hR
  have h2 : ((A : Matrix (Fin n) (Fin n) (ZMod 2)) * Rᵀ) * R = 1 := mul_eq_one_comm.mp h1
  refine ⟨⟨(A : Matrix (Fin n) (Fin n) (ZMod 2)) * Rᵀ, R, h2, h1⟩, ?_⟩
  show ((A : Matrix (Fin n) (Fin n) (ZMod 2)) * Rᵀ) *
    ((A : Matrix (Fin n) (Fin n) (ZMod 2)) * Rᵀ)ᵀ = A
  rw [Matrix.transpose_mul, Matrix.transpose_transpose, hA, ← Matrix.mul_assoc, h2, Matrix.one_mul]

end CFSG.ASVolI.ChH
