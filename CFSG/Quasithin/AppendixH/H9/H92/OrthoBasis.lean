module

public import CFSG.Quasithin.AppendixH.H9.H93.Theta.OuterInvolution
public import CFSG.Quasithin.AppendixH.H9.H92.OrthoBasis.SymmetricCongruence

public section

open scoped Matrix

namespace CFSG.ASVolI.ChH

open CFSG.Quasithin CFSG.Open

private theorem transpose_eq_of_outer_involution {n : ℕ} (A : GL (Fin n) (ZMod 2))
    (h : (pairActN n A * swapN n) * (pairActN n A * swapN n) = 1) :
    (A : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ = A := by
  have h1 : (A : Matrix (Fin n) (Fin n) (ZMod 2)) *
      ((dualGLn n A : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) = 1 := by
    refine Matrix.ext_of_mulVec_single fun j => ?_
    rw [← Matrix.mulVec_mulVec, outer_involution_mulVec_dual A h, Matrix.one_mulVec]
  rw [dualGLn_val] at h1
  have h2 : ((A⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *
      (A : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ = 1 := by
    have h3 := congrArg Matrix.transpose h1
    rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at h3
  calc (A : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ
      = ((A : Matrix (Fin n) (Fin n) (ZMod 2)) *
          ((A⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2))) *
          (A : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ := by
        rw [Units.mul_inv, Matrix.one_mul]
    _ = A := by rw [Matrix.mul_assoc, h2, Matrix.mul_one]

private theorem pairActN_mul_swapN_mul_inv {n : ℕ} (B A : GL (Fin n) (ZMod 2))
    (hB : (B : Matrix (Fin n) (Fin n) (ZMod 2)) * (B : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ = A) :
    pairActN n B * swapN n * (pairActN n B)⁻¹ = pairActN n A * swapN n := by
  have hBA : B * dualGLn n B⁻¹ = A :=
    Units.ext (by rw [Units.val_mul, dualGLn_val, inv_inv]; exact hB)
  calc pairActN n B * swapN n * (pairActN n B)⁻¹
      = pairActN n B * (swapN n * pairActN n B⁻¹) := by rw [mul_assoc, map_inv]
    _ = pairActN n B * (pairActN n (dualGLn n B⁻¹) * swapN n) := by rw [swapN_mul_pairActN]
    _ = pairActN n (B * dualGLn n B⁻¹) * swapN n := by rw [← mul_assoc, ← map_mul]
    _ = pairActN n A * swapN n := by rw [hBA]

theorem isConjIn_swap_of_outer_involution (t : MulAut (PairN 5)) (ht : t ∈ Mg 5) (htL : t ∉ Lg 5)
    (ht2 : orderOf t = 2) : IsConjIn (Mg 5) (swapN 5) t := by
  rcases mem_Mg_iff.mp ht with htL' | ⟨A, rfl⟩
  · exact absurd htL' htL
  · have htt : (pairActN 5 A * swapN 5) * (pairActN 5 A * swapN 5) = 1 := by
      have h := pow_orderOf_eq_one (pairActN 5 A * swapN 5)
      rwa [ht2, pow_two] at h
    obtain ⟨B, hB⟩ := exists_unit_mul_transpose_eq (by decide : Odd 5) A
      (transpose_eq_of_outer_involution A htt)
    exact ⟨pairActN 5 B, Lg_le_Mg (pairActN_mem_Lg B), pairActN_mul_swapN_mul_inv B A hB⟩

end CFSG.ASVolI.ChH
