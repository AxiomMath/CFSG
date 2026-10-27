module

public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.StandardType

abbrev GGPoly := List (ℤ × ℕ × ℕ)

namespace GGPoly

@[expose] def ins (c : ℤ) (i j : ℕ) : GGPoly → GGPoly
  | [] => if c = 0 then [] else [(c, i, j)]
  | (d, k, l) :: P =>
    if Nat.blt i k || (Nat.beq i k && Nat.blt j l) then
      (if c = 0 then (d, k, l) :: P else (c, i, j) :: (d, k, l) :: P)
    else if Nat.beq i k && Nat.beq j l then
      (if c + d = 0 then P else (c + d, k, l) :: P)
    else (d, k, l) :: ins c i j P

@[expose] def add (P Q : GGPoly) : GGPoly := P.foldr (fun t acc => ins t.1 t.2.1 t.2.2 acc) Q

@[expose] def neg (P : GGPoly) : GGPoly := P.map fun t => (-t.1, t.2)

@[expose] def sub (P Q : GGPoly) : GGPoly := add P (neg Q)

@[expose] def mulTerm (c : ℤ) (i j : ℕ) (P : GGPoly) : GGPoly :=
  P.map fun t => (c * t.1, i + t.2.1, j + t.2.2)

@[expose] def mul (P Q : GGPoly) : GGPoly :=
  P.foldr (fun t acc => add (mulTerm t.1 t.2.1 t.2.2 Q) acc) []

@[expose] def const (c : ℤ) : GGPoly := if c = 0 then [] else [(c, 0, 0)]

@[expose] def U : GGPoly := [(1, 1, 0)]

@[expose] def V : GGPoly := [(1, 0, 1)]

section Eval

variable {S : Type} [CommRing S] (u v : S)

@[expose] def eval (P : GGPoly) : S :=
  P.foldr (fun t acc => (t.1 : S) * u ^ t.2.1 * v ^ t.2.2 + acc) 0

@[simp] theorem eval_nil : eval u v [] = 0 := rfl

@[simp] theorem eval_cons (c : ℤ) (i j : ℕ) (P : GGPoly) :
    eval u v ((c, i, j) :: P) = (c : S) * u ^ i * v ^ j + eval u v P := rfl

theorem eval_ins (c : ℤ) (i j : ℕ) (P : GGPoly) :
    eval u v (ins c i j P) = (c : S) * u ^ i * v ^ j + eval u v P := by
  induction P with
  | nil =>
    unfold ins
    split_ifs with hc
    · simp [hc]
    · simp
  | cons t P ih =>
    obtain ⟨d, k, l⟩ := t
    unfold ins
    split_ifs with h1 hc h2 hcd
    · simp [hc]
    · simp
    · have hik : i = k ∧ j = l := by simpa [Nat.beq_eq] using h2
      obtain ⟨rfl, rfl⟩ := hik
      have hd : (d : S) = -c := by
        have : (d : ℤ) = -c := by omega
        rw [this, Int.cast_neg]
      simp [hd]
    · have hik : i = k ∧ j = l := by simpa [Nat.beq_eq] using h2
      obtain ⟨rfl, rfl⟩ := hik
      simp only [eval_cons, Int.cast_add]
      ring
    · simp only [eval_cons, ih]
      ring

theorem eval_add (P Q : GGPoly) : eval u v (add P Q) = eval u v P + eval u v Q := by
  induction P with
  | nil => simp [add]
  | cons t P ih =>
    obtain ⟨c, i, j⟩ := t
    have h : add ((c, i, j) :: P) Q = ins c i j (add P Q) := rfl
    rw [h, eval_ins, ih, eval_cons]
    ring

theorem eval_neg (P : GGPoly) : eval u v (neg P) = -eval u v P := by
  induction P with
  | nil => simp [neg]
  | cons t P ih =>
    obtain ⟨c, i, j⟩ := t
    have h : neg ((c, i, j) :: P) = (-c, i, j) :: neg P := rfl
    rw [h, eval_cons, eval_cons, ih, Int.cast_neg]
    ring

theorem eval_sub (P Q : GGPoly) : eval u v (sub P Q) = eval u v P - eval u v Q := by
  rw [sub, eval_add, eval_neg, sub_eq_add_neg]

theorem eval_mulTerm (c : ℤ) (i j : ℕ) (P : GGPoly) :
    eval u v (mulTerm c i j P) = (c : S) * u ^ i * v ^ j * eval u v P := by
  induction P with
  | nil => simp [mulTerm]
  | cons t P ih =>
    obtain ⟨d, k, l⟩ := t
    have h : mulTerm c i j ((d, k, l) :: P) = (c * d, i + k, j + l) :: mulTerm c i j P := rfl
    rw [h, eval_cons, eval_cons, ih, Int.cast_mul, pow_add, pow_add]
    ring

theorem eval_mul (P Q : GGPoly) : eval u v (mul P Q) = eval u v P * eval u v Q := by
  induction P with
  | nil => simp [mul]
  | cons t P ih =>
    obtain ⟨c, i, j⟩ := t
    have h : mul ((c, i, j) :: P) Q = add (mulTerm c i j Q) (mul P Q) := rfl
    rw [h, eval_add, eval_mulTerm, ih, eval_cons]
    ring

theorem eval_const (c : ℤ) : eval u v (const c) = (c : S) := by
  unfold const
  split_ifs with hc
  · simp [hc]
  · simp

@[simp] theorem eval_U : eval u v U = u := by simp [U]

@[simp] theorem eval_V : eval u v V = v := by simp [V]

theorem eval_eq_zero_of_eq_nil {P : GGPoly} (h : P = []) : eval u v P = 0 := by
  rw [h, eval_nil]

end Eval

end GGPoly

end CFSG.StandardType
