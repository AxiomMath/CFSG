module

public import CFSG.RankThree.GF2n.Smith81.S81BA5Def

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.A5Cube

open Matrix exteriorPower CFSG.Open CFSG.RankThree.GF2n.Smith81.EGeom

variable (K : Type) [Field K]

@[expose] def S0 : Submodule K (Fin 6 → K) where
  carrier := {v | ∀ j : Fin 6, j.val % 2 = 1 → v j = 0}
  add_mem' := fun ha hb j hj => by simp [ha j hj, hb j hj]
  zero_mem' := fun _ _ => rfl
  smul_mem' := fun c _ hv j hj => by simp [hv j hj]

@[expose] def UnipGL (S : Submodule K (Fin 6 → K)) : Subgroup (GL (Fin 6) K) where
  carrier := {g | (g : Matrix (Fin 6) (Fin 6) K).det = 1 ∧
    (∀ v, (g : Matrix (Fin 6) (Fin 6) K).mulVec v - v ∈ S) ∧
    ∀ s ∈ S, (g : Matrix (Fin 6) (Fin 6) K).mulVec s = s}
  mul_mem' := by
    rintro a b ⟨ha1, ha2, ha3⟩ ⟨hb1, hb2, hb3⟩
    refine ⟨?_, fun v => ?_, fun s hs => ?_⟩
    · simp [Matrix.det_mul, ha1, hb1]
    · have h1 := ha2 ((b : Matrix (Fin 6) (Fin 6) K).mulVec v)
      have h2 := hb2 v
      have h3 : (a : Matrix (Fin 6) (Fin 6) K).mulVec ((b : Matrix (Fin 6) (Fin 6) K).mulVec v) -
          v = ((a : Matrix (Fin 6) (Fin 6) K).mulVec ((b : Matrix (Fin 6) (Fin 6) K).mulVec v) -
            (b : Matrix (Fin 6) (Fin 6) K).mulVec v) +
            ((b : Matrix (Fin 6) (Fin 6) K).mulVec v - v) := by abel
      rw [Units.val_mul, ← Matrix.mulVec_mulVec, h3]
      exact S.add_mem h1 h2
    · rw [Units.val_mul, ← Matrix.mulVec_mulVec, hb3 s hs, ha3 s hs]
  one_mem' := by
    refine ⟨by simp, fun v => by simp, fun s _ => by simp⟩
  inv_mem' := by
    rintro a ⟨ha1, ha2, ha3⟩
    have hinv : ∀ s ∈ S, ((a⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).mulVec s = s := by
      intro s hs
      have h := ha3 s hs
      calc ((a⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).mulVec s
          = ((a⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).mulVec
              ((a : Matrix (Fin 6) (Fin 6) K).mulVec s) := by rw [h]
        _ = s := by
          rw [Matrix.mulVec_mulVec]
          simp
    refine ⟨?_, fun v => ?_, hinv⟩
    · have : ((a⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
          ((a : Matrix (Fin 6) (Fin 6) K))⁻¹ := by simp
      rw [this, Matrix.det_nonsing_inv, ha1]
      simp
    · have h1 := ha2 (((a⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).mulVec v)
      rw [Matrix.mulVec_mulVec] at h1
      simp only [Units.mul_inv, Matrix.one_mulVec] at h1
      have h2 := S.neg_mem h1
      simpa using h2

@[expose] def Urad (S : Submodule K (Fin 6 → K)) : Subgroup (Cube K ≃ₗ[K] Cube K) :=
  (UnipGL K S).map (rhoEquiv K)

end CFSG.RankThree.GF2n.Smith81.A5Cube
