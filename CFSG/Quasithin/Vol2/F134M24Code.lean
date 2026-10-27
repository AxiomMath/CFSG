module

public import CFSG.Quasithin.Vol2.F134PermCode

public section

namespace CFSG.Quasithin.F134

open Equiv

@[expose] def mul24 (x y : ℕ) : ℕ :=
  Nat.add (dig5 x (dig5 y 0)) (Nat.mul 32 (Nat.add (dig5 x (dig5 y 1)) (Nat.mul 32 (Nat.add (dig5 x
  (dig5 y 2)) (Nat.mul 32 (Nat.add (dig5 x (dig5 y 3)) (Nat.mul 32 (Nat.add (dig5 x (dig5 y 4))
  (Nat.mul 32 (Nat.add (dig5 x (dig5 y 5)) (Nat.mul 32 (Nat.add (dig5 x (dig5 y 6)) (Nat.mul 32
  (Nat.add (dig5 x (dig5 y 7)) (Nat.mul 32 (Nat.add (dig5 x (dig5 y 8)) (Nat.mul 32 (Nat.add (dig5 x
  (dig5 y 9)) (Nat.mul 32 (Nat.add (dig5 x (dig5 y 10)) (Nat.mul 32 (Nat.add (dig5 x (dig5 y 11))
  (Nat.mul 32 (Nat.add (dig5 x (dig5 y 12)) (Nat.mul 32 (Nat.add (dig5 x (dig5 y 13)) (Nat.mul 32
  (Nat.add (dig5 x (dig5 y 14)) (Nat.mul 32 (Nat.add (dig5 x (dig5 y 15)) (Nat.mul 32 (Nat.add (dig5
  x (dig5 y 16)) (Nat.mul 32 (Nat.add (dig5 x (dig5 y 17)) (Nat.mul 32 (Nat.add (dig5 x (dig5 y 18))
  (Nat.mul 32 (Nat.add (dig5 x (dig5 y 19)) (Nat.mul 32 (Nat.add (dig5 x (dig5 y 20)) (Nat.mul 32
  (Nat.add (dig5 x (dig5 y 21)) (Nat.mul 32 (Nat.add (dig5 x (dig5 y 22)) (Nat.mul 32 (Nat.add (dig5
  x (dig5 y 23)) (Nat.mul 32 0)))))))))))))))))))))))))))))))))))))))))))))))

theorem mul24_eq (x y : ℕ) :
    mul24 x y = ofDigs (2 ^ 5) (List.ofFn fun k : Fin 24 => digW 5 x (digW 5 y k)) := by
  simp only [List.ofFn_succ, List.ofFn_zero, ofDigs]
  rfl

theorem permCode_mul24 (σ τ : Perm (Fin 24)) :
    permCode (σ * τ) = mul24 (permCode σ) (permCode τ) := by
  rw [mul24_eq]
  have key : ∀ k : Fin 24, digW 5 (permCode σ) (digW 5 (permCode τ) k) = ((σ * τ) k : ℕ) := by
    intro k
    rw [digW_permCode (by norm_num) τ k, digW_permCode (by norm_num) σ (τ k)]
    rfl
  simp only [key]
  rfl

@[expose] def powC24 (one : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => one
  | k + 1, x => mul24 (powC24 one k x) x

theorem permCode_pow24 (σ : Perm (Fin 24)) (k : ℕ) :
    permCode (σ ^ k) = powC24 (permCode (1 : Perm (Fin 24))) k (permCode σ) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ, permCode_mul24, ih, powC24]

@[expose] def sqC24 : ℕ → ℕ → ℕ
  | 0, x => x
  | k + 1, x => sqC24 k (mul24 x x)

theorem permCode_pow_two_pow24 (k : ℕ) : ∀ σ : Perm (Fin 24),
    permCode (σ ^ 2 ^ k) = sqC24 k (permCode σ) := by
  induction k with
  | zero => intro σ; rw [pow_zero, pow_one]; rfl
  | succ k ih =>
    intro σ
    rw [pow_succ', pow_mul, sq, ih, permCode_mul24]
    rfl

theorem eq_of_permCode24 {σ τ : Perm (Fin 24)} (h : permCode σ = permCode τ) : σ = τ :=
  permCode_injective (by norm_num) h

end CFSG.Quasithin.F134
