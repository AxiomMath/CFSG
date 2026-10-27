module

public import CFSG.Permutation.FinPackPow
public import CFSG.Permutation.FinPackList

public section

namespace CFSG.Quasithin.H13.A6K

open Equiv CFSG.Permutation.FinPack

@[expose] def EC : ℕ := 5517840

@[expose] def IC : ℕ := 4530945

@[expose] def CC : List ℕ :=
  [5517840, 1070130, 3280980, 5509170, 3298320, 1061460, 5517825, 87090, 3277140, 5505330,
    3298305, 78420, 5514000, 1070115, 2297940, 5509155, 2315280, 1057620, 5513985, 87075,
    2294100, 5505315, 2315265, 74580, 4534800, 1066290, 3280965, 4526130, 3294480, 1061445,
    4534785, 83250, 3277125, 4522290, 3294465, 78405, 4530960, 1066275, 2297925, 4526115,
    2311440, 1057605, 4530945, 83235, 2294085, 4522275, 2311425, 74565]

@[expose] def A4C : List ℕ :=
  [5517840, 5513985, 4534785, 4530960, 1070130, 1066275, 87075, 83250, 3280980, 3277125,
    2297925, 2294100]

@[expose] def E0C : List ℕ := [5517840, 5513985, 4534785, 4530960]

@[expose] def E8C : List ℕ :=
  [5517840, 5517825, 5514000, 5513985, 4534800, 4534785, 4530960, 4530945]

theorem enc_one6 : enc (1 : Perm (Fin 6)) = EC := by decide +kernel

variable {n : ℕ}

theorem beq_pow_of_eq (hn : n ≤ 16) {e : ℕ} (he : enc (1 : Perm (Fin n)) = e)
    {σ : Perm (Fin n)} {k : ℕ} (h : σ ^ k = 1) : Nat.beq (powK n e (enc σ) k) e = true := by
  rw [← enc_pow hn he, h, he, Nat.beq_refl]

theorem eq_of_beq_pow (hn : n ≤ 16) {e : ℕ} (he : enc (1 : Perm (Fin n)) = e)
    {σ : Perm (Fin n)} {k : ℕ} (h : Nat.beq (powK n e (enc σ) k) e = true) : σ ^ k = 1 := by
  rw [← enc_pow hn he, ← he] at h
  exact (beq_enc_iff hn).1 h

theorem beq_one_false (hn : n ≤ 16) {e : ℕ} (he : enc (1 : Perm (Fin n)) = e)
    {σ : Perm (Fin n)} (h : σ ≠ 1) : Nat.beq (enc σ) e = false := by
  rw [← he]
  exact beq_enc_false hn h

theorem length_filter_enc {L : List (Perm (Fin n))} {C : List ℕ} (hL : (L.map enc == C) = true)
    (p : Perm (Fin n) → Bool) (q : ℕ → Bool) (hpq : ∀ σ, p σ = q (enc σ)) :
    (L.filter p).length = (C.filter q).length := by
  rw [beq_iff_eq] at hL
  subst hL
  rw [List.filter_map, List.length_map]
  exact congrArg List.length (List.filter_congr fun σ _ => hpq σ)

theorem norm_A4 : allK (fun c => !Nat.beq (powK 6 EC c 3) EC || Nat.beq c EC ||
    Nat.beq (CC.filter fun s => Nat.beq (mulK 6 (mulK 6 s c) (invPK 6 s)) c ||
      Nat.beq (mulK 6 (mulK 6 s c) (invPK 6 s)) (invPK 6 c)).length 12) A4C = true := by
  decide +kernel

@[expose] noncomputable def commC (c d : ℕ) : ℕ :=
  mulK 6 (mulK 6 (mulK 6 c d) (invPK 6 c)) (invPK 6 d)

theorem comm_CC : allK (fun c => Nat.beq (mulK 6 c IC) (mulK 6 IC c)) CC = true := by
  decide +kernel

theorem walk_CC : walkK 6 (fun c => !Nat.beq (mulK 6 c IC) (mulK 6 IC c) || memK c CC) 6 0 0 0 =
    true := by
  decide +kernel

theorem exp_CC :allK (fun c => Nat.beq (powK 6 EC c 12) EC) CC = true := by decide +kernel

theorem c3_CC : allK (fun c => !Nat.beq (powK 6 EC c 3) EC || memK c A4C) CC = true := by
  decide +kernel

theorem mul_A4 : mulInK 6 A4C A4C = true := by decide +kernel

theorem mul_E8 : mulInK 6 E8C E8C = true := by decide +kernel

theorem mul_E0 : mulInK 6 E0C E0C = true := by decide +kernel

theorem inv_A4 : allK (fun c => memK (invPK 6 c) A4C) A4C = true := by decide +kernel

theorem inv_E8 : allK (fun c => memK (invPK 6 c) E8C) E8C = true := by decide +kernel

theorem sub_E0E8 : subKL E0C E8C = true := by decide +kernel

theorem norm_A4E0 :
    allK (fun a => allK (fun x => memK (mulK 6 (mulK 6 a x) (invPK 6 a)) E0C) E0C) A4C = true := by
  decide +kernel

theorem exp_A4 : allK (fun c => Nat.beq (powK 6 EC c 6) EC) A4C = true := by decide +kernel

theorem two_A4 : allK (fun c => !Nat.beq (powK 6 EC c 2) EC || memK c E0C) A4C = true := by
  decide +kernel

theorem sq_E0 : sqKL 6 EC E0C = true := by decide +kernel

theorem e0two_A4 : allK (fun c => !Nat.beq (powK 6 EC c 3) EC || Nat.beq c EC ||
    allK (fun d => !Nat.beq (powK 6 EC d 3) EC || Nat.beq d EC || Nat.beq d c ||
      Nat.beq d (invPK 6 c) || (memK (commC c d) E0C &&
        allK (fun x => Nat.beq x EC || Nat.beq x (commC c d) ||
          Nat.beq x (mulK 6 (mulK 6 c (commC c d)) (invPK 6 c)) ||
          Nat.beq x (mulK 6 (mulK 6 (invPK 6 c) (commC c d)) c)) E0C)) A4C) A4C = true := by
  decide +kernel

theorem e8c3_A4 : allK (fun c => !Nat.beq (powK 6 EC c 3) EC || Nat.beq c EC ||
    allK (fun x => !Nat.beq (powK 6 EC x 4) EC || memK x E8C ||
      !Nat.beq (powK 6 EC (mulK 6 x (mulK 6 (mulK 6 c x) (invPK 6 c))) 4) EC) CC) A4C =
    true := by
  decide +kernel

end CFSG.Quasithin.H13.A6K
