module

public import CFSG.Permutation.FinPackCount

public section

namespace CFSG.Permutation.FinPack

open Equiv Finset

@[expose] noncomputable def powK (n e c k : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) e (fun _ p => mulK n p c) k

@[expose] noncomputable def supK (n c : ℕ) : ℕ :=
  sumLtK (fun i => Bool.rec (motive := fun _ => ℕ) 1 0 (Nat.beq (rd c i) i)) n

@[expose] noncomputable def disjK (n c d : ℕ) : Bool :=
  allLtK (fun i => Bool.rec (motive := fun _ => Bool) (Nat.beq (rd d i) i) true
    (Nat.beq (rd c i) i)) n

@[expose] noncomputable def invPK (n c : ℕ) : ℕ :=
  encF (fun v => sumLtK (fun i => Bool.rec (motive := fun _ => ℕ) 0 i (Nat.beq (rd c i) v)) n) n

variable {n : ℕ}

theorem bitI_eq (hn : n ≤ 16) (σ : Perm (Fin n)) {v : ℕ} (hv : v < n) (i : Fin n) :
    (Bool.rec (motive := fun _ => ℕ) 0 (i : ℕ) (Nat.beq (rd (enc σ) i) v) : ℕ) =
      if σ⁻¹ ⟨v, hv⟩ = i then (i : ℕ) else 0 := by
  rw [rd_enc hn σ i]
  by_cases h : σ⁻¹ ⟨v, hv⟩ = i
  · rw [if_pos h]
    have e : (σ i : ℕ) = v := by
      rw [← h]
      exact congrArg Fin.val (σ.apply_symm_apply ⟨v, hv⟩)
    rw [e, Nat.beq_refl]
  · rw [if_neg h]
    have e : Nat.beq (σ i : ℕ) v = false := Bool.eq_false_iff.2 fun e => h (by
      have e' : σ i = ⟨v, hv⟩ := Fin.ext (Nat.eq_of_beq_eq_true e)
      rw [← e']
      exact σ.symm_apply_apply i)
    rw [e]

theorem enc_inv (hn : n ≤ 16) (σ : Perm (Fin n)) : enc σ⁻¹ = invPK n (enc σ) := by
  rw [invPK]
  conv_lhs => rw [enc]
  refine encF_congr fun v hv => ?_
  try dsimp only
  rw [dif_pos hv, sumLtK_eq, ← Fin.sum_univ_eq_sum_range
      (fun i => (Bool.rec (motive := fun _ => ℕ) 0 i (Nat.beq (rd (enc σ) i) v) : ℕ)) n,
    Finset.sum_congr rfl fun i _ => bitI_eq hn σ hv i, Finset.sum_ite_eq,
    if_pos (Finset.mem_univ _)]

theorem enc_pow (hn : n ≤ 16) {e : ℕ} (he : enc (1 : Perm (Fin n)) = e) (σ : Perm (Fin n)) (k : ℕ) :
    enc (σ ^ k) = powK n e (enc σ) k := by
  induction k with
  | zero => rw [pow_zero, he]; rfl
  | succ k ih =>
    rw [pow_succ, enc_mul hn, ih]
    rfl

theorem beq_rd_iff (hn : n ≤ 16) (σ : Perm (Fin n)) (i : Fin n) :
    Nat.beq (rd (enc σ) i) i = true ↔ σ i = i := by
  rw [Nat.beq_eq, rd_enc hn σ i]
  exact ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩

theorem bitS_eq (hn : n ≤ 16) (σ : Perm (Fin n)) (i : Fin n) :
    (Bool.rec (motive := fun _ => ℕ) 1 0 (Nat.beq (rd (enc σ) i) i) : ℕ) =
      if σ i ≠ i then 1 else 0 := by
  by_cases h : σ i = i
  · rw [if_neg (not_not.2 h), (beq_rd_iff hn σ i).2 h]
  · rw [if_pos h, Bool.eq_false_iff.2 fun e => h ((beq_rd_iff hn σ i).1 e)]

theorem card_support_eq_supK (hn : n ≤ 16) (σ : Perm (Fin n)) :
    σ.support.card = supK n (enc σ) := by
  rw [supK, sumLtK_eq, ← Fin.sum_univ_eq_sum_range
      (fun i => (Bool.rec (motive := fun _ => ℕ) 1 0 (Nat.beq (rd (enc σ) i) i) : ℕ)) n,
    Finset.card_eq_sum_ones, Perm.support, Finset.sum_filter]
  exact Finset.sum_congr rfl fun i _ => (bitS_eq hn σ i).symm

theorem disjoint_support_iff (hn : n ≤ 16) (σ τ : Perm (Fin n)) :
    Disjoint σ.support τ.support ↔ disjK n (enc σ) (enc τ) = true := by
  rw [Finset.disjoint_left, disjK, allLtK_iff]
  constructor
  · intro H j hj
    have e1 : Nat.beq (rd (enc σ) j) j = true ↔ σ ⟨j, hj⟩ = ⟨j, hj⟩ := beq_rd_iff hn σ ⟨j, hj⟩
    have e2 : Nat.beq (rd (enc τ) j) j = true ↔ τ ⟨j, hj⟩ = ⟨j, hj⟩ := beq_rd_iff hn τ ⟨j, hj⟩
    by_cases h : σ ⟨j, hj⟩ = ⟨j, hj⟩
    · rw [e1.2 h]
    · have h2 : τ ⟨j, hj⟩ = ⟨j, hj⟩ := by
        have := H (Perm.mem_support.2 h)
        rwa [Perm.mem_support, not_not] at this
      rw [Bool.eq_false_iff.2 fun e => h (e1.1 e)]
      exact e2.2 h2
  · intro H i hi h2
    rw [Perm.mem_support] at hi h2
    have : Bool.rec (motive := fun _ => Bool) (Nat.beq (rd (enc τ) i) i) true
        (Nat.beq (rd (enc σ) i) i) = true := H i i.isLt
    rw [Bool.eq_false_iff.2 fun e => hi ((beq_rd_iff hn σ i).1 e)] at this
    exact h2 ((beq_rd_iff hn τ i).1 this)

end CFSG.Permutation.FinPack
