module

public import CFSG.Permutation.FinPackWalk

public section

namespace CFSG.Permutation.FinPack

open Equiv

variable {n : ℕ}

@[expose] noncomputable def commLaneK (n c d : ℕ) : Bool :=
  allLtK (fun i => Nat.beq (rd c (rd d i)) (rd d (rd c i))) n

theorem commLaneK_iff (hn : n ≤ 16) (σ τ : Perm (Fin n)) :
    commLaneK n (enc σ) (enc τ) = true ↔ σ * τ = τ * σ := by
  rw [commLaneK, allLtK_iff]
  constructor
  · intro h
    refine Equiv.ext fun i => Fin.ext ?_
    have e := h i i.2
    rw [Nat.beq_eq, rd_enc hn τ i, rd_enc hn σ i, rd_enc hn σ (τ i), rd_enc hn τ (σ i)] at e
    rw [Perm.mul_apply, Perm.mul_apply]
    exact e
  · intro h i hi
    have e := congrArg (fun g : Perm (Fin n) => ((g ⟨i, hi⟩ : Fin n) : ℕ)) h
    simp only [Perm.mul_apply] at e
    have h1 : rd (enc τ) i = τ ⟨i, hi⟩ := rd_enc hn τ ⟨i, hi⟩
    have h2 : rd (enc σ) i = σ ⟨i, hi⟩ := rd_enc hn σ ⟨i, hi⟩
    rw [Nat.beq_eq, h1, h2, rd_enc hn σ, rd_enc hn τ]
    exact e

end CFSG.Permutation.FinPack
