module

public import CFSG.Quasithin.AppendixH.H9.H92.RadHom

public section

open scoped Matrix

namespace CFSG.ASVolI.ChH

open CFSG.Quasithin CFSG.Open

private theorem add_self_pi_zmod2 {n : ℕ} (a : Fin n → ZMod 2) : a + a = 0 :=
  funext fun i => CharTwo.add_self_eq_zero (a i)

theorem radMat_val_mul_self {n : ℕ} {D : Submodule (ZMod 2) (Fin n → ZMod 2)}
    {B : GL (Fin n) (ZMod 2)} (hB : B ∈ RadMat n D) :
    (B : Matrix (Fin n) (Fin n) (ZMod 2)) * (B : Matrix (Fin n) (Fin n) (ZMod 2)) = 1 := by
  have hN : (B : Matrix (Fin n) (Fin n) (ZMod 2)) - 1 ∈ radNil n D :=
    (mem_radMat_iff_sub_mem_radNil B).mp hB
  have hNN : ((B : Matrix (Fin n) (Fin n) (ZMod 2)) - 1) *
      ((B : Matrix (Fin n) (Fin n) (ZMod 2)) - 1) = 0 := radNil_mul_radNil hN hN
  have h2 : ∀ M : Matrix (Fin n) (Fin n) (ZMod 2), M + M = 0 := by
    intro M
    ext i j
    simp only [Matrix.add_apply, Matrix.zero_apply]
    exact (by decide : ∀ c : ZMod 2, c + c = 0) _
  have e : (B : Matrix (Fin n) (Fin n) (ZMod 2)) * (B : Matrix (Fin n) (Fin n) (ZMod 2)) - 1 =
      ((B : Matrix (Fin n) (Fin n) (ZMod 2)) - 1) * ((B : Matrix (Fin n) (Fin n) (ZMod 2)) - 1) +
        (((B : Matrix (Fin n) (Fin n) (ZMod 2)) - 1) + ((B : Matrix (Fin n) (Fin n) (ZMod 2)) - 1)) := by
    noncomm_ring
  have hzero : (B : Matrix (Fin n) (Fin n) (ZMod 2)) * (B : Matrix (Fin n) (Fin n) (ZMod 2)) - 1 = 0 := by
    rw [e, hNN, h2, add_zero]
  exact sub_eq_zero.mp hzero

theorem pairActN_pairVec_of_mem_radMat {n : ℕ} {D : Submodule (ZMod 2) (Fin n → ZMod 2)}
    {B : GL (Fin n) (ZMod 2)} (hB : B ∈ RadMat n D) (a b : Fin n → ZMod 2) :
    pairActN n B (pairVec a b) =
      pairVec (a + ((B : Matrix (Fin n) (Fin n) (ZMod 2)) - 1) *ᵥ a)
        (b + ((B : Matrix (Fin n) (Fin n) (ZMod 2)) - 1)ᵀ *ᵥ b) := by
  have h1 := radMat_val_mul_self hB
  have hmul : B * B = 1 := Units.ext (by simpa using h1)
  have hinv : B⁻¹ = B := inv_eq_of_mul_eq_one_right hmul
  rw [pairActN_pairVec, dualGLn_val, hinv]
  apply pairVec_inj.mpr
  constructor
  · rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    abel
  · rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.sub_mulVec, Matrix.one_mulVec]
    abel

theorem pairActN_mul_inv_pairVec_of_mem_radMat {n : ℕ} {D : Submodule (ZMod 2) (Fin n → ZMod 2)}
    {B : GL (Fin n) (ZMod 2)} (hB : B ∈ RadMat n D) (a b : Fin n → ZMod 2) :
    pairActN n B (pairVec a b) * (pairVec a b)⁻¹ =
      pairVec (((B : Matrix (Fin n) (Fin n) (ZMod 2)) - 1) *ᵥ a)
        (((B : Matrix (Fin n) (Fin n) (ZMod 2)) - 1)ᵀ *ᵥ b) := by
  rw [pairActN_pairVec_of_mem_radMat hB, pairVec_inv, pairVec_mul]
  apply pairVec_inj.mpr
  constructor
  · calc (a + ((B : Matrix (Fin n) (Fin n) (ZMod 2)) - 1) *ᵥ a) + a
        = (a + a) + ((B : Matrix (Fin n) (Fin n) (ZMod 2)) - 1) *ᵥ a := by abel
      _ = ((B : Matrix (Fin n) (Fin n) (ZMod 2)) - 1) *ᵥ a := by
            rw [add_self_pi_zmod2, zero_add]
  · calc (b + ((B : Matrix (Fin n) (Fin n) (ZMod 2)) - 1)ᵀ *ᵥ b) + b
        = (b + b) + ((B : Matrix (Fin n) (Fin n) (ZMod 2)) - 1)ᵀ *ᵥ b := by abel
      _ = ((B : Matrix (Fin n) (Fin n) (ZMod 2)) - 1)ᵀ *ᵥ b := by
            rw [add_self_pi_zmod2, zero_add]

end CFSG.ASVolI.ChH
