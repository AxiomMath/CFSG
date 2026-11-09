module

public import CFSG.Permutation.FinPackPow
public import CFSG.Permutation.FinPackComm
public import CFSG.Permutation.FinPackList
public import CFSG.Permutation.FinPackInv

public section

namespace CFSG.Permutation.FinPack

open Equiv

variable {n : ℕ}

theorem beq_enc_eq_decide (hn : n ≤ 16) (σ τ : Perm (Fin n)) :
    Nat.beq (enc σ) (enc τ) = decide (σ = τ) := by
  rw [Bool.eq_iff_iff, beq_enc_iff hn, decide_eq_true_iff]

theorem evenK_enc_eq_decide (hn : n ≤ 16) (σ : Perm (Fin n)) :
    evenK n (enc σ) = decide (Perm.sign σ = 1) := by
  rw [Bool.eq_iff_iff, ← sign_eq_one_iff_evenK hn, decide_eq_true_iff]

theorem commLaneK_enc_eq_decide (hn : n ≤ 16) (σ τ : Perm (Fin n)) :
    commLaneK n (enc σ) (enc τ) = decide (σ * τ = τ * σ) := by
  rw [Bool.eq_iff_iff, commLaneK_iff hn, decide_eq_true_iff]

theorem mulK_enc (hn : n ≤ 16) (σ τ : Perm (Fin n)) : mulK n (enc σ) (enc τ) = enc (σ * τ) :=
  (enc_mul hn σ τ).symm

theorem invCK_enc (hn : n ≤ 16) (σ : Perm (Fin n)) : invCK n (enc σ) = enc σ⁻¹ :=
  (enc_inv_invCK hn σ).symm

theorem powK_enc (hn : n ≤ 16) (σ : Perm (Fin n)) (k : ℕ) :
    powK n (enc (1 : Perm (Fin n))) (enc σ) k = enc (σ ^ k) :=
  (enc_pow hn rfl σ k).symm

theorem exists_of_anyK_valid {P : ℕ → Bool} {L : List ℕ}
    (h : anyK (fun d => permValidK n d && P d) L = true) :
    ∃ σ : Perm (Fin n), P (enc σ) = true := by
  obtain ⟨d, -, hd⟩ := anyK_iff.1 h
  rw [Bool.and_eq_true] at hd
  obtain ⟨σ, rfl⟩ := exists_enc_of_permValidK hd.1
  exact ⟨σ, hd.2⟩

end CFSG.Permutation.FinPack
