module

public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

public section

namespace CFSG.Permutation.FinPack

open Equiv

@[expose] def rd (c i : ℕ) : ℕ := Nat.land (Nat.shiftRight c (Nat.mul 4 i)) 15

@[expose] noncomputable def encF (a : ℕ → ℕ) (k : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0 (fun i acc => Nat.add acc (Nat.shiftLeft (a i) (Nat.mul 4 i))) k

theorem encF_zero (a : ℕ → ℕ) : encF a 0 = 0 := rfl

theorem encF_succ (a : ℕ → ℕ) (k : ℕ) : encF a (k + 1) = encF a k + a k * 16 ^ k := by
  change encF a k + a k <<< (4 * k) = _
  rw [Nat.shiftLeft_eq, pow_mul]
  norm_num

theorem rd_eq (c i : ℕ) : rd c i = c / 16 ^ i % 16 := by
  change (c >>> (4 * i)) &&& (2 ^ 4 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, pow_mul]
  norm_num

theorem encF_lt {a : ℕ → ℕ} {k : ℕ} (h : ∀ i < k, a i < 16) : encF a k < 16 ^ k := by
  induction k with
  | zero => simp [encF_zero]
  | succ k ih =>
    rw [encF_succ, pow_succ]
    have h1 := ih fun i hi => h i (by omega)
    have h2 : a k * 16 ^ k ≤ 15 * 16 ^ k := Nat.mul_le_mul_right _ (by have := h k (by omega); omega)
    linarith

theorem rd_encF {a : ℕ → ℕ} {k : ℕ} (h : ∀ i < k, a i < 16) {j : ℕ} (hj : j < k) :
    rd (encF a k) j = a j := by
  rw [rd_eq]
  induction k with
  | zero => omega
  | succ k ih =>
    rw [encF_succ]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · have ih' := ih (fun i hi => h i (by omega)) hj
      have hk : a k * 16 ^ k = 16 ^ j * (16 * (16 ^ (k - j - 1) * a k)) := by
        have e : 16 ^ k = 16 ^ j * 16 ^ (k - j - 1) * 16 := by
          rw [← pow_add, ← pow_succ]
          congr 1
          omega
        rw [e]
        ring
      rw [hk, Nat.add_mul_div_left _ _ (by positivity), Nat.add_mul_mod_self_left, ih']
    · rw [mul_comm, Nat.add_mul_div_left _ _ (by positivity),
        Nat.div_eq_of_lt (encF_lt fun i hi => h i (by omega)), zero_add,
        Nat.mod_eq_of_lt (h j (by omega))]

theorem encF_congr {a b : ℕ → ℕ} {k : ℕ} (h : ∀ i < k, a i = b i) : encF a k = encF b k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [encF_succ, encF_succ, ih fun i hi => h i (by omega), h k (by omega)]

variable {n : ℕ}

@[expose] noncomputable def enc (σ : Perm (Fin n)) : ℕ :=
  encF (fun i => if h : i < n then (σ ⟨i, h⟩ : ℕ) else 0) n

@[expose] noncomputable def mulK (n c d : ℕ) : ℕ := encF (fun i => rd c (rd d i)) n

theorem rd_enc (hn : n ≤ 16) (σ : Perm (Fin n)) (i : Fin n) : rd (enc σ) i = σ i := by
  rw [enc, rd_encF (fun j hj => by rw [dif_pos hj]; exact lt_of_lt_of_le (Fin.isLt _) hn) i.isLt]
  simp

theorem enc_mul (hn : n ≤ 16) (σ τ : Perm (Fin n)) : enc (σ * τ) = mulK n (enc σ) (enc τ) := by
  rw [mulK]
  conv_lhs => rw [enc]
  refine encF_congr fun i hi => ?_
  have h1 : rd (enc τ) i = τ ⟨i, hi⟩ := rd_enc hn τ ⟨i, hi⟩
  rw [dif_pos hi, Perm.mul_apply, h1, rd_enc hn σ]

theorem enc_inj (hn : n ≤ 16) {σ τ : Perm (Fin n)} (h : enc σ = enc τ) : σ = τ :=
  Equiv.ext fun i => Fin.ext (by rw [← rd_enc hn σ i, ← rd_enc hn τ i, h])

theorem mem_iff_enc (hn : n ≤ 16) (L : List (Perm (Fin n))) (σ : Perm (Fin n)) :
    σ ∈ L ↔ enc σ ∈ L.map enc := by
  rw [List.mem_map]
  exact ⟨fun h => ⟨σ, h, rfl⟩, fun ⟨τ, hτ, e⟩ => enc_inj hn e ▸ hτ⟩

@[expose] noncomputable def memK (c : ℕ) (L : List ℕ) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun a _ r => Nat.beq a c || r) L

@[expose] noncomputable def allK (f : ℕ → Bool) (L : List ℕ) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun a _ r => f a && r) L

@[expose] noncomputable def anyK (f : ℕ → Bool) (L : List ℕ) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun a _ r => f a || r) L

theorem memK_iff {c : ℕ} {L : List ℕ} : memK c L = true ↔ c ∈ L := by
  induction L with
  | nil => simp [memK]
  | cons a L ih =>
    change (Nat.beq a c || memK c L) = true ↔ _
    rw [Bool.or_eq_true, ih, Nat.beq_eq, List.mem_cons, eq_comm]

theorem allK_iff {f : ℕ → Bool} {L : List ℕ} : allK f L = true ↔ ∀ a ∈ L, f a = true := by
  induction L with
  | nil => simp [allK]
  | cons a L ih =>
    change (f a && allK f L) = true ↔ _
    rw [Bool.and_eq_true, ih, List.forall_mem_cons]

theorem anyK_iff {f : ℕ → Bool} {L : List ℕ} : anyK f L = true ↔ ∃ a ∈ L, f a = true := by
  induction L with
  | nil => simp [anyK]
  | cons a L ih =>
    change (f a || anyK f L) = true ↔ _
    rw [Bool.or_eq_true, ih]
    simp

end CFSG.Permutation.FinPack
