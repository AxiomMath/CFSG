module

public import CFSG.RankThree.PartTwo.Toolkit.RawGL

public section

namespace CFSG.RankThree.PartTwo.Toolkit.Raw

@[expose] def dg (x q : ℕ) : ℕ := Nat.mod (Nat.div x q) 3

@[expose] def nent (a b c d e f : ℕ) : ℕ :=
  Nat.mod (Nat.add (Nat.add (Nat.mul a b) (Nat.mul c d)) (Nat.mul e f)) 3

@[expose] def nmul (x y : ℕ) : ℕ :=
  Nat.add (nent (dg x 1) (dg y 1) (dg x 3) (dg y 27) (dg x 9) (dg y 729)) (Nat.mul 3
  (Nat.add (nent (dg x 1) (dg y 3) (dg x 3) (dg y 81) (dg x 9) (dg y 2187)) (Nat.mul 3
  (Nat.add (nent (dg x 1) (dg y 9) (dg x 3) (dg y 243) (dg x 9) (dg y 6561)) (Nat.mul 3
  (Nat.add (nent (dg x 27) (dg y 1) (dg x 81) (dg y 27) (dg x 243) (dg y 729)) (Nat.mul 3
  (Nat.add (nent (dg x 27) (dg y 3) (dg x 81) (dg y 81) (dg x 243) (dg y 2187)) (Nat.mul 3
  (Nat.add (nent (dg x 27) (dg y 9) (dg x 81) (dg y 243) (dg x 243) (dg y 6561)) (Nat.mul 3
  (Nat.add (nent (dg x 729) (dg y 1) (dg x 2187) (dg y 27) (dg x 6561) (dg y 729)) (Nat.mul 3
  (Nat.add (nent (dg x 729) (dg y 3) (dg x 2187) (dg y 81) (dg x 6561) (dg y 2187)) (Nat.mul 3
  (nent (dg x 729) (dg y 9) (dg x 2187) (dg y 243) (dg x 6561) (dg y 6561)))))))))))))))))

@[expose] def ndet (x : ℕ) : ℕ :=
  (dg x 1 * dg x 81 * dg x 6561 + 2 * (dg x 1 * dg x 243 * dg x 2187) +
    2 * (dg x 3 * dg x 27 * dg x 6561) + dg x 3 * dg x 243 * dg x 729 +
    dg x 9 * dg x 27 * dg x 2187 + 2 * (dg x 9 * dg x 81 * dg x 729)) % 3

@[expose] def npow (x k : ℕ) : ℕ := Nat.rec (motive := fun _ => ℕ) 6643 (fun _ r => nmul x r) k

theorem code_rone : code rone = 6643 := rfl

theorem dg_eq (x q : ℕ) : dg x q = x / q % 3 := rfl

theorem nent_eq (a b c d e f : ℕ) : nent a b c d e f = (a * b + c * d + e * f) % 3 := rfl

section Digits

variable (x : R9)

theorem code_d0 : dg (code x) 1 = x.a.val := by
  have := val_lt_three x.a; have := val_lt_three x.b; have := val_lt_three x.c
  have := val_lt_three x.d; have := val_lt_three x.e; have := val_lt_three x.f
  have := val_lt_three x.g; have := val_lt_three x.h; have := val_lt_three x.i
  rw [dg_eq]; unfold code; omega

theorem code_d1 : dg (code x) 3 = x.b.val := by
  have := val_lt_three x.a; have := val_lt_three x.b; have := val_lt_three x.c
  have := val_lt_three x.d; have := val_lt_three x.e; have := val_lt_three x.f
  have := val_lt_three x.g; have := val_lt_three x.h; have := val_lt_three x.i
  rw [dg_eq]; unfold code; omega

theorem code_d2 : dg (code x) 9 = x.c.val := by
  have := val_lt_three x.a; have := val_lt_three x.b; have := val_lt_three x.c
  have := val_lt_three x.d; have := val_lt_three x.e; have := val_lt_three x.f
  have := val_lt_three x.g; have := val_lt_three x.h; have := val_lt_three x.i
  rw [dg_eq]; unfold code; omega

theorem code_d3 : dg (code x) 27 = x.d.val := by
  have := val_lt_three x.a; have := val_lt_three x.b; have := val_lt_three x.c
  have := val_lt_three x.d; have := val_lt_three x.e; have := val_lt_three x.f
  have := val_lt_three x.g; have := val_lt_three x.h; have := val_lt_three x.i
  rw [dg_eq]; unfold code; omega

theorem code_d4 : dg (code x) 81 = x.e.val := by
  have := val_lt_three x.a; have := val_lt_three x.b; have := val_lt_three x.c
  have := val_lt_three x.d; have := val_lt_three x.e; have := val_lt_three x.f
  have := val_lt_three x.g; have := val_lt_three x.h; have := val_lt_three x.i
  rw [dg_eq]; unfold code; omega

theorem code_d5 : dg (code x) 243 = x.f.val := by
  have := val_lt_three x.a; have := val_lt_three x.b; have := val_lt_three x.c
  have := val_lt_three x.d; have := val_lt_three x.e; have := val_lt_three x.f
  have := val_lt_three x.g; have := val_lt_three x.h; have := val_lt_three x.i
  rw [dg_eq]; unfold code; omega

theorem code_d6 : dg (code x) 729 = x.g.val := by
  have := val_lt_three x.a; have := val_lt_three x.b; have := val_lt_three x.c
  have := val_lt_three x.d; have := val_lt_three x.e; have := val_lt_three x.f
  have := val_lt_three x.g; have := val_lt_three x.h; have := val_lt_three x.i
  rw [dg_eq]; unfold code; omega

theorem code_d7 : dg (code x) 2187 = x.h.val := by
  have := val_lt_three x.a; have := val_lt_three x.b; have := val_lt_three x.c
  have := val_lt_three x.d; have := val_lt_three x.e; have := val_lt_three x.f
  have := val_lt_three x.g; have := val_lt_three x.h; have := val_lt_three x.i
  rw [dg_eq]; unfold code; omega

theorem code_d8 : dg (code x) 6561 = x.i.val := by
  have := val_lt_three x.a; have := val_lt_three x.b; have := val_lt_three x.c
  have := val_lt_three x.d; have := val_lt_three x.e; have := val_lt_three x.f
  have := val_lt_three x.g; have := val_lt_three x.h; have := val_lt_three x.i
  rw [dg_eq]; unfold code; omega

end Digits

theorem val_nent (a b c d e f : ZMod 3) :
    (a * b + c * d + e * f).val = nent a.val b.val c.val d.val e.val f.val := by
  rw [nent_eq, ← ZMod.val_natCast (n := 3)]
  congr 1
  push_cast
  simp only [ZMod.natCast_zmod_val]

theorem nmul_code (x y : R9) : nmul (code x) (code y) = code (rmul x y) := by
  simp only [nmul, code_d0, code_d1, code_d2, code_d3, code_d4, code_d5, code_d6, code_d7,
    code_d8, Nat.add_eq, Nat.mul_eq]
  simp only [code, rmul, val_nent]

theorem ndet_code (x : R9) : ndet (code x) = (rdet x).val := by
  simp only [ndet, code_d0, code_d1, code_d2, code_d3, code_d4, code_d5, code_d6, code_d7,
    code_d8]
  rw [← ZMod.val_natCast (n := 3)]
  congr 1
  push_cast
  simp only [ZMod.natCast_zmod_val, rdet]
  have h3 : (3 : ZMod 3) = 0 := rfl
  linear_combination (x.a * x.f * x.h + x.b * x.d * x.i + x.c * x.e * x.g) * h3

theorem npow_code (x : R9) (k : ℕ) : npow (code x) k = code (rpowR x k) := by
  induction k with
  | zero => rw [rpowR, code_rone]; rfl
  | succ k ih =>
    change nmul (code x) (npow (code x) k) = _
    rw [ih, rpowR, nmul_code]

end CFSG.RankThree.PartTwo.Toolkit.Raw

end
