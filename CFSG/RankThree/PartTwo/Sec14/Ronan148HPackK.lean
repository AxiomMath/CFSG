module

public import CFSG.Permutation.FinPackComm
public import CFSG.Permutation.FinPackWalk

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148HPackK

open Equiv Equiv.Perm CFSG.Permutation.FinPack

@[expose] noncomputable def centSqB (C E : ℕ) (LC : List ℕ) (d : ℕ) : Bool :=
  !evenK 7 d || ((commLaneK 7 d C && Nat.beq (mulK 7 d d) E) == memK d LC)

theorem cent_sq_iff_of_walk {C E : ℕ} {LC : List ℕ} {c : Perm (Fin 7)} (L : List (Perm (Fin 7)))
    (hC : enc c = C) (hE : enc (1 : Perm (Fin 7)) = E) (hL : L.map enc = LC)
    (hw : walkK 7 (centSqB C E LC) 7 0 0 0 = true)
    (σ : Perm (Fin 7)) (hs : Perm.sign σ = 1) : (σ * c = c * σ ∧ σ ^ 2 = 1 ↔ σ ∈ L) := by
  have h := walkK_sound hw σ
  have he : evenK 7 (enc σ) = true := (sign_eq_one_iff_evenK (by norm_num) σ).1 hs
  simp only [centSqB, he, Bool.not_true, Bool.false_or, beq_iff_eq] at h
  rw [mem_iff_enc (by norm_num), hL, ← memK_iff, ← h, Bool.and_eq_true, ← hC,
    commLaneK_iff (by norm_num), ← hE, ← enc_mul (by norm_num), beq_enc_iff (by norm_num), sq]

theorem enc_one7 : enc (1 : Perm (Fin 7)) = 106181136 := by decide +kernel

theorem enc_c012 : enc (swap 0 1 * swap 1 2 : Perm (Fin 7)) = 106180641 := by decide +kernel

theorem enc_c345 : enc (swap 3 4 * swap 4 5 : Perm (Fin 7)) = 104153616 := by decide +kernel

theorem v1L_enc : ([1, swap 3 4 * swap 5 6, swap 3 5 * swap 4 6, swap 3 6 * swap 4 5] :
    List (Perm (Fin 7))).map enc = [106181136, 90391056, 70668816, 54878736] := by decide +kernel

theorem v2L_enc : ([1, swap 0 1 * swap 2 6, swap 0 2 * swap 1 6, swap 0 6 * swap 1 2] :
    List (Perm (Fin 7))).map enc = [106181136, 39073281, 22294626, 5517606] := by decide +kernel

theorem v1_walk : walkK 7 (centSqB 106180641 106181136 [106181136, 90391056, 70668816, 54878736])
    7 0 0 0 = true := by decide +kernel

theorem v2_walk : walkK 7 (centSqB 104153616 106181136 [106181136, 39073281, 22294626, 5517606])
    7 0 0 0 = true := by decide +kernel

theorem v1_iff (σ : Perm (Fin 7)) (hs : Perm.sign σ = 1) :
    (σ * (swap 0 1 * swap 1 2) = (swap 0 1 * swap 1 2) * σ ∧ σ ^ 2 = 1 ↔
      σ ∈ ([1, swap 3 4 * swap 5 6, swap 3 5 * swap 4 6, swap 3 6 * swap 4 5] :
        List (Perm (Fin 7)))) :=
  cent_sq_iff_of_walk _ enc_c012 enc_one7 v1L_enc v1_walk σ hs

theorem v2_iff (σ : Perm (Fin 7)) (hs : Perm.sign σ = 1) :
    (σ * (swap 3 4 * swap 4 5) = (swap 3 4 * swap 4 5) * σ ∧ σ ^ 2 = 1 ↔
      σ ∈ ([1, swap 0 1 * swap 2 6, swap 0 2 * swap 1 6, swap 0 6 * swap 1 2] :
        List (Perm (Fin 7)))) :=
  cent_sq_iff_of_walk _ enc_c345 enc_one7 v2L_enc v2_walk σ hs

end CFSG.RankThree.PartTwo.Sec14.Ronan148HPackK
