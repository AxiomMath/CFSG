module

public import CFSG.Certificates.Kernel.Spor.PCountWSound

public section

namespace CFSG.Permutation.FinPack64

open Equiv CFSG.KS.PCnt CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def mulW (n p q : ℕ) : ℕ := pcomp n 6 (mask 6) p q

@[expose] noncomputable def selK (b o c : ℕ) : ℕ := Nat.rec (motive := fun _ => ℕ) o (fun _ _ => c) b

@[expose] noncomputable def all2 (f : ℕ → Bool) : Bool :=
  Bool.rec (motive := fun _ => Bool) false (f (nat_lit 1)) (f (nat_lit 0))

@[expose] noncomputable def any2 (f : ℕ → Bool) : Bool :=
  Bool.rec (motive := fun _ => Bool) (f (nat_lit 1)) true (f (nat_lit 0))

theorem all2_spec {f : ℕ → Bool} (h : all2 f = true) {b : ℕ} (hb : b < 2) : f b = true := by
  unfold all2 at h
  cases h0 : f 0 <;> rw [h0] at h
  · exact absurd h Bool.false_ne_true
  · interval_cases b
    · exact h0
    · exact h

theorem any2_spec {f : ℕ → Bool} (h : any2 f = true) : ∃ b < 2, f b = true := by
  unfold any2 at h
  cases h0 : f 0 <;> rw [h0] at h
  · exact ⟨1, by omega, h⟩
  · exact ⟨0, by omega, h0⟩

theorem brec_true {a b : Bool} (h : Bool.rec (motive := fun _ => Bool) a b true = true) :
    b = true := h

theorem brec_false {a b : Bool} (h : Bool.rec (motive := fun _ => Bool) a b false = true) :
    a = true := h

variable {n : ℕ} {σ τ c x y : Perm (Fin n)} {a b o C X Y : ℕ}

private theorem hw6 (hn : n ≤ 64) : n ≤ 2 ^ 6 := le_trans hn (by norm_num)

theorem pk_mul (hn : n ≤ 64) (ha : pkw 6 σ = a) (hb : pkw 6 τ = b) :
    pkw 6 (σ * τ) = mulW n a b := by
  rw [← ha, ← hb, mulW, pkw_mul (hw6 hn) (lt_of_le_of_lt hn (by norm_num))]

theorem eq_of_pk (hn : n ≤ 64) (ha : pkw 6 σ = a) (hb : pkw 6 τ = b) (h : a = b) : σ = τ :=
  pkw_inj (hw6 hn) (by rw [ha, hb, h])

theorem beq_false_of_ne (hn : n ≤ 64) (ha : pkw 6 σ = a) (hb : pkw 6 τ = b) (h : σ ≠ τ) :
    Nat.beq a b = false := by
  cases e : Nat.beq a b
  · rfl
  · exact absurd (eq_of_pk hn ha hb (Nat.eq_of_beq_eq_true e)) h

theorem ne_of_pk (ha : pkw 6 σ = a) (hb : pkw 6 τ = b) (h : Nat.beq a b = false) : σ ≠ τ := by
  intro e
  rw [e, hb] at ha
  rw [ha, Nat.beq_refl] at h
  exact Bool.noConfusion h

theorem conj_of (hn : n ≤ 64) (hc : pkw 6 c = C) (hx : pkw 6 x = X) (hy : pkw 6 y = Y)
    (h : mulW n C X = mulW n Y C) : c * x * c⁻¹ = y := by
  have e : c * x = y * c := eq_of_pk hn (pk_mul hn hc hx) (pk_mul hn hy hc) h
  rw [e, mul_inv_cancel_right]

theorem pk_conj (hn : n ≤ 64) (hc : pkw 6 c = C) (hci : pkw 6 c⁻¹ = Y) (hx : pkw 6 x = X) :
    pkw 6 (c * x * c⁻¹) = mulW n (mulW n C X) Y :=
  pk_mul hn (pk_mul hn hc hx) hci

theorem brec_or {a b : Bool} (h : Bool.rec (motive := fun _ => Bool) a true b = true) :
    b = true ∨ a = true := by
  cases b
  · exact Or.inr h
  · exact Or.inl rfl

theorem pk_pow (ho : pkw 6 (1 : Perm (Fin n)) = o) (ha : pkw 6 σ = a) (i : Fin 2) :
    pkw 6 (σ ^ (i : ℕ)) = selK i o a := by
  rcases i with ⟨_ | _ | k, hi⟩
  · change pkw 6 (σ ^ 0) = o
    rw [pow_zero]
    exact ho
  · change pkw 6 (σ ^ 1) = a
    rw [pow_one]
    exact ha
  · omega

theorem sq_of (hn : n ≤ 64) (ha : pkw 6 σ = a) (hb : pkw 6 τ = b)
    (h : mulW n a a = mulW n b b) : σ ^ 2 = τ ^ 2 := by
  rw [pow_two, pow_two]
  exact eq_of_pk hn (pk_mul hn ha ha) (pk_mul hn hb hb) h

@[expose] noncomputable def powW (n o a k : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) o (fun _ r => mulW n r a) k

theorem pk_npow (hn : n ≤ 64) (ho : pkw 6 (1 : Perm (Fin n)) = o) (ha : pkw 6 σ = a) (k : ℕ) :
    pkw 6 (σ ^ k) = powW n o a k := by
  induction k with
  | zero =>
    rw [pow_zero]
    exact ho
  | succ k ih =>
    rw [pow_succ]
    exact pk_mul hn ih ha

theorem pow_eq_one_of (hn : n ≤ 64) (ho : pkw 6 (1 : Perm (Fin n)) = o) (ha : pkw 6 σ = a)
    (k : ℕ) (h : powW n o a k = o) : σ ^ k = 1 :=
  eq_of_pk hn (pk_npow hn ho ha k) ho h

theorem comm_mul_of {G : Type*} [Group G] {a b c v : G} (hc : c * c = 1)
    (h : a * b = v * c * b * a) : a * b * a⁻¹ * b⁻¹ * c = v := by
  rw [h, mul_inv_cancel_right, mul_inv_cancel_right, mul_assoc, hc, mul_one]

theorem pow_four_of (hn : n ≤ 64) (ho : pkw 6 (1 : Perm (Fin n)) = o) (ha : pkw 6 σ = a)
    (h : mulW n (mulW n (mulW n a a) a) a = o) : σ ^ 4 = 1 := by
  have e : σ ^ 4 = σ * σ * σ * σ := by rw [pow_succ, pow_succ, pow_succ, pow_one]
  rw [e]
  exact eq_of_pk hn (pk_mul hn (pk_mul hn (pk_mul hn ha ha) ha) ha) ho h

end CFSG.Permutation.FinPack64
