module

public import CFSG.Quasithin.AppendixH.H9.ModelBasic

public section

open scoped Matrix

namespace CFSG.ASVolI.ChH

open CFSG.Quasithin CFSG.Open

variable {n : ℕ}

private theorem dotProduct_self_eq_dotProduct_ones (x : Fin n → ZMod 2) :
    x ⬝ᵥ x = x ⬝ᵥ (fun _ => 1) := by
  refine Finset.sum_congr rfl fun i _ => ?_
  exact (by decide : ∀ z : ZMod 2, z * z = z * 1) (x i)

theorem dualGLn_eq_self_iff {B : GL (Fin n) (ZMod 2)} :
    dualGLn n B = B ↔
      (B : Matrix (Fin n) (Fin n) (ZMod 2)) * (B : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ = 1 := by
  rw [Units.ext_iff, dualGLn_val]
  constructor
  · intro h
    have h' : ((B⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) =
        (B : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ := by
      simpa [Matrix.transpose_transpose] using congrArg Matrix.transpose h
    rw [← h', ← Units.val_mul, mul_inv_cancel, Units.val_one]
  · intro h
    have h' : ((B⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) =
        (B : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ := Units.inv_eq_of_mul_eq_one_right h
    rw [h', Matrix.transpose_transpose]

theorem mem_inf_centralizer_swap_iff {g : MulAut (PairN n)} :
    g ∈ Lg n ⊓ Subgroup.centralizer ({swapN n} : Set (MulAut (PairN n))) ↔
      ∃ B : GL (Fin n) (ZMod 2),
        (B : Matrix (Fin n) (Fin n) (ZMod 2)) * (B : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ = 1 ∧
          g = pairActN n B := by
  constructor
  · intro hg
    obtain ⟨hL, hC⟩ := Subgroup.mem_inf.mp hg
    obtain ⟨B, rfl⟩ := mem_Lg_iff.mp hL
    refine ⟨B, dualGLn_eq_self_iff.mp ?_, rfl⟩
    have h := Subgroup.mem_centralizer_iff.mp hC (swapN n) (Set.mem_singleton _)
    rw [swapN_mul_pairActN] at h
    exact pairActN_injective (mul_right_cancel h)
  · rintro ⟨B, hB, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨pairActN_mem_Lg B, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    rw [swapN_mul_pairActN, dualGLn_eq_self_iff.mpr hB]

theorem pairActN_pairVec_of_orth {B : GL (Fin n) (ZMod 2)}
    (hB : (B : Matrix (Fin n) (Fin n) (ZMod 2)) * (B : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ = 1)
    (a b : Fin n → ZMod 2) :
    pairActN n B (pairVec a b) = pairVec ((B : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ a)
      ((B : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ b) := by
  rw [pairActN_pairVec, dualGLn_eq_self_iff.mpr hB]

private theorem orth_dotProduct {B : Matrix (Fin n) (Fin n) (ZMod 2)} (h : B * Bᵀ = 1)
    (x y : Fin n → ZMod 2) : (B *ᵥ x) ⬝ᵥ (B *ᵥ y) = x ⬝ᵥ y := by
  have h' : Bᵀ * B = 1 := mul_eq_one_comm.mp h
  rw [Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose B x, Matrix.vecMul_vecMul, h',
    Matrix.vecMul_one]

theorem orth_mulVec_ones {B : Matrix (Fin n) (Fin n) (ZMod 2)} (h : B * Bᵀ = 1) :
    B *ᵥ (fun _ => (1 : ZMod 2)) = fun _ => 1 := by
  funext i
  have h1 : B *ᵥ (Bᵀ *ᵥ Pi.single i (1 : ZMod 2)) = Pi.single i 1 := by
    rw [Matrix.mulVec_mulVec, h, Matrix.one_mulVec]
  have h2 := orth_dotProduct h (Bᵀ *ᵥ Pi.single i (1 : ZMod 2)) (fun _ => 1)
  have h3 := orth_dotProduct h (Bᵀ *ᵥ Pi.single i (1 : ZMod 2)) (Bᵀ *ᵥ Pi.single i (1 : ZMod 2))
  rw [h1] at h2 h3
  rw [dotProduct_self_eq_dotProduct_ones (Bᵀ *ᵥ Pi.single i (1 : ZMod 2))] at h3
  rw [← h2] at h3
  simpa [single_dotProduct] using h3.symm

theorem orth_sum_mulVec {B : Matrix (Fin n) (Fin n) (ZMod 2)} (h : B * Bᵀ = 1)
    (a : Fin n → ZMod 2) : ∑ i, (B *ᵥ a) i = ∑ i, a i := by
  have h1 := orth_dotProduct h (fun _ => 1) a
  rw [orth_mulVec_ones h] at h1
  simpa [dotProduct] using h1

theorem exists_orth_mulVec_single_add (c : Fin n → ZMod 2) (hc : ∑ i, c i = 0) (i : Fin n)
    (hi : c i = 1) :
    ∃ B : GL (Fin n) (ZMod 2),
      (B : Matrix (Fin n) (Fin n) (ZMod 2)) * (B : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ = 1 ∧
        (B : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ Pi.single i 1 + Pi.single i 1 = c := by
  have hcc : c ⬝ᵥ c = 0 := by
    rw [dotProduct_self_eq_dotProduct_ones]
    simpa [dotProduct] using hc
  have hPP : Matrix.vecMulVec c c * Matrix.vecMulVec c c = 0 := by
    rw [Matrix.vecMulVec_mul_vecMulVec, hcc, zero_smul, Matrix.vecMulVec_zero]
  have hP2 : Matrix.vecMulVec c c + Matrix.vecMulVec c c = 0 := by
    ext j k
    simp only [Matrix.add_apply, Matrix.vecMulVec_apply, Matrix.zero_apply]
    exact CharTwo.add_self_eq_zero _
  have hMM : (1 + Matrix.vecMulVec c c) * (1 + Matrix.vecMulVec c c) = 1 := by
    have h1 : (1 + Matrix.vecMulVec c c) * (1 + Matrix.vecMulVec c c) =
        1 + (Matrix.vecMulVec c c + Matrix.vecMulVec c c) +
          Matrix.vecMulVec c c * Matrix.vecMulVec c c := by
      noncomm_ring
    rw [h1, hP2, hPP, add_zero, add_zero]
  have hMt : (1 + Matrix.vecMulVec c c)ᵀ = 1 + Matrix.vecMulVec c c := by
    rw [Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_vecMulVec]
  refine ⟨⟨1 + Matrix.vecMulVec c c, 1 + Matrix.vecMulVec c c, hMM, hMM⟩, ?_, ?_⟩
  · change (1 + Matrix.vecMulVec c c) * (1 + Matrix.vecMulVec c c)ᵀ = 1
    rw [hMt, hMM]
  · change (1 + Matrix.vecMulVec c c) *ᵥ Pi.single i 1 + Pi.single i 1 = c
    rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.vecMulVec_mulVec, dotProduct_single_one, hi]
    simp only [MulOpposite.op_one, one_smul]
    rw [add_comm (Pi.single i (1 : ZMod 2)) c, add_assoc]
    have : (Pi.single i (1 : ZMod 2) + Pi.single i 1 : Fin n → ZMod 2) = 0 := by
      funext j
      simpa using CharTwo.add_self_eq_zero ((Pi.single i (1 : ZMod 2) : Fin n → ZMod 2) j)
    rw [this, add_zero]

end CFSG.ASVolI.ChH
