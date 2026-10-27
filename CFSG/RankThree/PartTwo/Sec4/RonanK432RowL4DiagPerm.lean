module

public import Mathlib.LinearAlgebra.Matrix.Permutation
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open Matrix

namespace L4Diag

section Exponents

variable {K : Type} [Field K]

theorem pow_eq_pow_mod {ω : K} (hω3 : ω ^ 3 = 1) (r : ℕ) : ω ^ r = ω ^ (r % 3) := by
  conv_lhs => rw [← Nat.mod_add_div r 3]
  rw [pow_add, pow_mul, hω3, one_pow, mul_one]

theorem pow_eq_of_zmod_eq {ω : K} (hω3 : ω ^ 3 = 1) {m n : ℕ} (h : (m : ZMod 3) = n) :
    ω ^ m = ω ^ n := by
  rw [pow_eq_pow_mod hω3 m, pow_eq_pow_mod hω3 n, (ZMod.natCast_eq_natCast_iff' m n 3).mp h]

theorem zmod_eq_of_pow_eq {ω : K} (hprim : IsPrimitiveRoot ω 3) {m n : ℕ}
    (h : ω ^ m = ω ^ n) : (m : ZMod 3) = n := by
  rw [ZMod.natCast_eq_natCast_iff']
  apply hprim.pow_inj (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num))
  rw [← pow_eq_pow_mod hprim.pow_eq_one m, ← pow_eq_pow_mod hprim.pow_eq_one n]
  exact h

theorem pow_val_add {ω : K} (hprim : IsPrimitiveRoot ω 3) (x y : ZMod 3) :
    ω ^ (x + y).val = ω ^ x.val * ω ^ y.val := by
  rw [← pow_add]
  apply pow_eq_of_zmod_eq hprim.pow_eq_one
  simp only [Nat.cast_add, ZMod.natCast_zmod_val]

theorem eq_of_pow_val_eq {ω : K} (hprim : IsPrimitiveRoot ω 3) {x y : ZMod 3}
    (h : ω ^ x.val = ω ^ y.val) : x = y := by
  simpa only [ZMod.natCast_zmod_val] using zmod_eq_of_pow_eq hprim h

theorem pow_val_pow {ω : K} (hprim : IsPrimitiveRoot ω 3) (a : ZMod 3) (m : ℕ) :
    (ω ^ a.val) ^ m = ω ^ ((m : ZMod 3) * a).val := by
  rw [← pow_mul]
  apply pow_eq_of_zmod_eq hprim.pow_eq_one
  simp only [Nat.cast_mul, ZMod.natCast_zmod_val]
  rw [mul_comm]

theorem sub_const_of_pow_eq {ι : Type} {ω : K} (hprim : IsPrimitiveRoot ω 3) {a b : ι → ZMod 3}
    {k : ZMod 3} {c : K} (h : ∀ l, ω ^ (b l).val = c * ω ^ (k * a l).val) (l l' : ι) :
    b l - k * a l = b l' - k * a l' := by
  have hω0 : ω ≠ 0 := hprim.ne_zero (by norm_num)
  have hcancel : ∀ l, ω ^ (b l - k * a l).val = c := by
    intro l
    have hb : b l = (b l - k * a l) + k * a l := by ring
    have h1 := h l
    rw [hb, pow_val_add hprim] at h1
    exact mul_right_cancel₀ (pow_ne_zero _ hω0) h1
  exact eq_of_pow_val_eq hprim ((hcancel l).trans (hcancel l').symm)

end Exponents

section Signed

variable {K : Type} [Field K]

theorem permMatrix_apply' (σ : Equiv.Perm (Fin 4)) (r c : Fin 4) :
    σ.permMatrix K r c = if σ r = c then 1 else 0 := by
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]

theorem permMatrix_mul_diagonal (σ : Equiv.Perm (Fin 4)) (d : Fin 4 → K) :
    σ.permMatrix K * diagonal d = diagonal (fun r => d (σ r)) * σ.permMatrix K := by
  ext r c
  rw [mul_diagonal, diagonal_mul]
  simp only [permMatrix_apply']
  split_ifs with h
  · rw [h, one_mul, mul_one]
  · rw [zero_mul, mul_zero]

@[expose] noncomputable def signDiag (K : Type) [Field K] (i : Fin 4) : Matrix (Fin 4) (Fin 4) K :=
  diagonal fun k => if k = i then -1 else 1

theorem signDiag_mul_signDiag (i : Fin 4) : signDiag K i * signDiag K i = 1 := by
  unfold signDiag
  rw [diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext k
  split_ifs <;> norm_num

theorem signDiag_mul_diagonal_comm (i : Fin 4) (e : Fin 4 → K) :
    signDiag K i * diagonal e = diagonal e * signDiag K i := by
  unfold signDiag
  rw [diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  funext k
  exact mul_comm _ _

theorem det_signDiag (i : Fin 4) : (signDiag K i).det = -1 := by
  unfold signDiag
  rw [det_diagonal]
  simp

@[expose] noncomputable def signGL (K : Type) [Field K] (i : Fin 4) : GL (Fin 4) K :=
  Units.mk (signDiag K i) (signDiag K i) (signDiag_mul_signDiag i) (signDiag_mul_signDiag i)

@[expose] noncomputable def permGL4 (K : Type) [Field K] (σ : Equiv.Perm (Fin 4)) : GL (Fin 4) K :=
  Units.mk (σ.permMatrix K) (σ⁻¹.permMatrix K)
    (by rw [← permMatrix_mul, inv_mul_cancel, permMatrix_one])
    (by rw [← permMatrix_mul, mul_inv_cancel, permMatrix_one])

theorem det_swap_permMatrix {i j : Fin 4} (hij : i ≠ j) :
    ((Equiv.swap i j).permMatrix K).det = -1 := by
  rw [det_permutation, Equiv.Perm.sign_swap hij]
  simp

@[expose] noncomputable def signedSwap (K : Type) [Field K] (i j : Fin 4) : GL (Fin 4) K :=
  signGL K i * permGL4 K (Equiv.swap i j)

theorem coe_signedSwap (i j : Fin 4) :
    ((signedSwap K i j : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      signDiag K i * (Equiv.swap i j).permMatrix K :=
  rfl

theorem det_signedSwap {i j : Fin 4} (hij : i ≠ j) :
    ((signedSwap K i j : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).det = 1 := by
  rw [coe_signedSwap, det_mul, det_signDiag, det_swap_permMatrix hij]
  norm_num

theorem signedSwap_mul_diagonal (i j : Fin 4) (d : Fin 4 → K) :
    ((signedSwap K i j : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * diagonal d =
      diagonal (fun r => d (Equiv.swap i j r)) *
        ((signedSwap K i j : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
  rw [coe_signedSwap]
  calc signDiag K i * (Equiv.swap i j).permMatrix K * diagonal d
      = signDiag K i * ((Equiv.swap i j).permMatrix K * diagonal d) := by rw [mul_assoc]
    _ = signDiag K i * (diagonal (fun r => d (Equiv.swap i j r)) *
          (Equiv.swap i j).permMatrix K) := by rw [permMatrix_mul_diagonal]
    _ = (signDiag K i * diagonal (fun r => d (Equiv.swap i j r))) *
          (Equiv.swap i j).permMatrix K := by rw [mul_assoc]
    _ = (diagonal (fun r => d (Equiv.swap i j r)) * signDiag K i) *
          (Equiv.swap i j).permMatrix K := by rw [signDiag_mul_diagonal_comm]
    _ = diagonal (fun r => d (Equiv.swap i j r)) *
          (signDiag K i * (Equiv.swap i j).permMatrix K) := by rw [mul_assoc]

end Signed

end L4Diag

end CFSG.RankThree.PartTwo.Sec4.RonanK432

end
