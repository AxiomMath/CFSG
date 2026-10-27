module

public import CFSG.CharacterTheory.SteinbergBYAlternatingSixData

public section

namespace CFSG.Quasithin.G11.Harris.Alt6

open CFSG.CharacterTheory.SteinbergBY AlternatingSix Equiv Matrix

@[expose] def heartForm : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![0, 1, 0, 0; 1, 0, 1, 0; 0, 1, 0, 1; 0, 0, 1, 0]

theorem heartHom_form : ∀ π : Perm (Fin 6),
    (heartHom π)ᵀ * heartForm * heartHom π = heartForm := by decide +kernel

@[expose] def krylov (M : Matrix (Fin 4) (Fin 4) (ZMod 2)) (v : Fin 4 → ZMod 2) :
    Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  Matrix.of fun i j => ((M ^ (j : ℕ)) *ᵥ v) i

theorem eq_krylov_of_commute {M X N : Matrix (Fin 4) (Fin 4) (ZMod 2)} {v : Fin 4 → ZMod 2}
    (hN : krylov M v * N = 1) (hX : X * M = M * X) : X = krylov M (X *ᵥ v) * N := by
  have h1 : X * krylov M v = krylov M (X *ᵥ v) := by
    ext i j
    have hc : Commute X (M ^ (j : ℕ)) := (Commute.pow_right (show Commute X M from hX) _)
    have h2 : X *ᵥ ((M ^ (j : ℕ)) *ᵥ v) = (M ^ (j : ℕ)) *ᵥ (X *ᵥ v) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hc.eq]
    have h3 : (X * krylov M v) i j = (X *ᵥ ((M ^ (j : ℕ)) *ᵥ v)) i := by
      simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, krylov, Matrix.of_apply]
    rw [h3, h2]
    rfl
  calc X = X * (krylov M v * N) := by rw [hN, Matrix.mul_one]
    _ = X * krylov M v * N := by rw [Matrix.mul_assoc]
    _ = krylov M (X *ᵥ v) * N := by rw [h1]

@[expose] def cyc5 : Perm (Fin 6) := swap 0 1 * swap 1 2 * swap 2 3 * swap 3 4

@[expose] def cyc3 : Perm (Fin 6) := swap 0 1 * swap 1 2 * swap 3 4 * swap 4 5

theorem cyc5_mem : cyc5 ∈ alternatingGroup (Fin 6) := by
  rw [Perm.mem_alternatingGroup]; decide

theorem cyc3_mem : cyc3 ∈ alternatingGroup (Fin 6) := by
  rw [Perm.mem_alternatingGroup]; decide

theorem heartHom_cyc5 : heartHom cyc5 = !![0, 0, 0, 1; 1, 0, 0, 1; 0, 1, 0, 1; 0, 0, 1, 1] := by
  decide +kernel

theorem heartHom_cyc3 : heartHom cyc3 = !![0, 1, 1, 1; 1, 1, 1, 0; 0, 0, 1, 1; 0, 0, 1, 0] := by
  decide +kernel

theorem heartHom_total_cyc5 :
    heartHom (totalPermHom cyc5) = !![1, 0, 1, 0; 1, 1, 0, 1; 0, 0, 1, 1; 0, 1, 1, 0] := by
  decide +kernel

theorem heartHom_total_cyc3 :
    heartHom (totalPermHom cyc3) = !![0, 0, 1, 1; 1, 1, 1, 1; 1, 0, 0, 1; 1, 0, 0, 0] := by
  decide +kernel

theorem commutant_heart_a (X : Matrix (Fin 4) (Fin 4) (ZMod 2))
    (h5 : X * heartHom cyc5 = heartHom cyc5 * X) (h3 : X * heartHom cyc3 = heartHom cyc3 * X) :
    X = 0 ∨ X = 1 := by
  rw [heartHom_cyc5] at h5
  rw [heartHom_cyc3] at h3
  have hN : krylov !![0, 0, 0, 1; 1, 0, 0, 1; 0, 1, 0, 1; 0, 0, 1, 1] ![1, 0, 0, 0] * 1 = 1 := by
    decide
  have key := eq_krylov_of_commute hN h5
  rw [Matrix.mul_one] at key
  have : ∀ x : Fin 4 → ZMod 2,
      krylov !![0, 0, 0, 1; 1, 0, 0, 1; 0, 1, 0, 1; 0, 0, 1, 1] x *
          !![0, 1, 1, 1; 1, 1, 1, 0; 0, 0, 1, 1; 0, 0, 1, 0] =
        !![0, 1, 1, 1; 1, 1, 1, 0; 0, 0, 1, 1; 0, 0, 1, 0] *
          krylov !![0, 0, 0, 1; 1, 0, 0, 1; 0, 1, 0, 1; 0, 0, 1, 1] x →
      krylov !![0, 0, 0, 1; 1, 0, 0, 1; 0, 1, 0, 1; 0, 0, 1, 1] x = 0 ∨
        krylov !![0, 0, 0, 1; 1, 0, 0, 1; 0, 1, 0, 1; 0, 0, 1, 1] x = 1 := by decide +kernel
  rw [key] at h3 ⊢
  exact this _ h3

theorem commutant_heart_b (X : Matrix (Fin 4) (Fin 4) (ZMod 2))
    (h5 : X * heartHom (totalPermHom cyc5) = heartHom (totalPermHom cyc5) * X)
    (h3 : X * heartHom (totalPermHom cyc3) = heartHom (totalPermHom cyc3) * X) :
    X = 0 ∨ X = 1 := by
  rw [heartHom_total_cyc5] at h5
  rw [heartHom_total_cyc3] at h3
  have hN : krylov !![1, 0, 1, 0; 1, 1, 0, 1; 0, 0, 1, 1; 0, 1, 1, 0] ![1, 0, 0, 0] *
      !![1, 1, 1, 1; 0, 1, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0] = 1 := by decide
  have key := eq_krylov_of_commute hN h5
  have : ∀ x : Fin 4 → ZMod 2,
      krylov !![1, 0, 1, 0; 1, 1, 0, 1; 0, 0, 1, 1; 0, 1, 1, 0] x *
          !![1, 1, 1, 1; 0, 1, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0] *
          !![0, 0, 1, 1; 1, 1, 1, 1; 1, 0, 0, 1; 1, 0, 0, 0] =
        !![0, 0, 1, 1; 1, 1, 1, 1; 1, 0, 0, 1; 1, 0, 0, 0] *
          (krylov !![1, 0, 1, 0; 1, 1, 0, 1; 0, 0, 1, 1; 0, 1, 1, 0] x *
            !![1, 1, 1, 1; 0, 1, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0]) →
      krylov !![1, 0, 1, 0; 1, 1, 0, 1; 0, 0, 1, 1; 0, 1, 1, 0] x *
          !![1, 1, 1, 1; 0, 1, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0] = 0 ∨
        krylov !![1, 0, 1, 0; 1, 1, 0, 1; 0, 0, 1, 1; 0, 1, 1, 0] x *
          !![1, 1, 1, 1; 0, 1, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0] = 1 := by decide +kernel
  rw [key] at h3 ⊢
  exact this _ h3

end CFSG.Quasithin.G11.Harris.Alt6
