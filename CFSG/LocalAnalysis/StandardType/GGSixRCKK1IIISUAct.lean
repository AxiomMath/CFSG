module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IIISUActAux3

public section

namespace CFSG.StandardType.RCKK1IIISU

open Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

variable {k : ℕ}
theorem rckSU_act (hk : 4 ≤ k) (τ : SUF ≃+* SUF) (B : GL (Fin k) SUF)
    (hB : conjTr SUσ (B : Matrix (Fin k) (Fin k) SUF) * antidiag k *
      (B : Matrix (Fin k) (Fin k) SUF) = antidiag k)
    (hr : (B : Matrix (Fin k) (Fin k) SUF) *
      ((suR hk : GL (Fin k) SUF) : Matrix (Fin k) (Fin k) SUF).map τ *
        ((B⁻¹ : GL (Fin k) SUF) : Matrix (Fin k) (Fin k) SUF) =
      ((suR hk : GL (Fin k) SUF) : Matrix (Fin k) (Fin k) SUF)) :
    ∃ ψ : GL (Fin 4) (ZMod 2),
      (∀ v : Fin 4 → ZMod 2,
        s5q ((ψ : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec v) = s5q v) ∧
      (ψ : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec s5R = s5R ∧
      (τ = RingEquiv.refl SUF → ψ ≠ s5tau) ∧
      ∀ v : Fin 4 → ZMod 2,
        (B : Matrix (Fin k) (Fin k) SUF) * (suCorner hk v).map τ *
            ((B⁻¹ : GL (Fin k) SUF) : Matrix (Fin k) (Fin k) SUF) =
          suCorner hk ((ψ : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec v) := by
  have hB' : conjTr SUσ (B : Matrix (Fin k) (Fin k) SUF) * rckSUc_J k *
      (B : Matrix (Fin k) (Fin k) SUF) = rckSUc_J k := hB
  have hBB : ((B⁻¹ : GL (Fin k) SUF) : Matrix (Fin k) (Fin k) SUF) *
      (B : Matrix (Fin k) (Fin k) SUF) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hτr : (((suR hk : GL (Fin k) SUF)) : Matrix (Fin k) (Fin k) SUF).map τ
      = ((suR hk : GL (Fin k) SUF) : Matrix (Fin k) (Fin k) SUF) := by
    rw [rckSUc_suR_eq hk, rckSUc_map_add, rckSUc_map_one_k hk, rckSUc_N_map]
  have hr' : (B : Matrix (Fin k) (Fin k) SUF) *
        ((suR hk : GL (Fin k) SUF) : Matrix (Fin k) (Fin k) SUF) *
        ((B⁻¹ : GL (Fin k) SUF) : Matrix (Fin k) (Fin k) SUF)
      = ((suR hk : GL (Fin k) SUF) : Matrix (Fin k) (Fin k) SUF) := by
    rwa [hτr] at hr
  have h1 : (B : Matrix (Fin k) (Fin k) SUF) * (1 + rckSUc_N hk)
      = (1 + rckSUc_N hk) * (B : Matrix (Fin k) (Fin k) SUF) := by
    have h2 := congrArg (fun X => X * (B : Matrix (Fin k) (Fin k) SUF)) hr'
    rw [rckSUc_suR_eq hk] at h2
    rwa [Matrix.mul_assoc, Matrix.mul_assoc, hBB, Matrix.mul_one] at h2
  have hBN : (B : Matrix (Fin k) (Fin k) SUF) * rckSUc_N hk
      = rckSUc_N hk * (B : Matrix (Fin k) (Fin k) SUF) := by
    have h2 := h1
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, Matrix.one_mul] at h2
    exact add_left_cancel h2
  exact ⟨rckSUc_psi hk B τ hB' hBN,
    rckSUc_q_preserved hk B τ hB' hBN,
    rckSUc_psi_fixed_R hk B τ hB' hBN hr,
    fun hrefl => rckSUc_ne_tau hk B τ hB' hBN hrefl,
    rckSUc_conj_corner_Binv hk B τ hB' hBN⟩

end CFSG.StandardType.RCKK1IIISU
