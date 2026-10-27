module

public import CFSG.Quasithin.Vol2.F134PermCode

public section

namespace CFSG.Quasithin.F134

open Equiv

@[expose] def mul23 (x y : ℕ) : ℕ :=
  Nat.add (dig5 x (dig5 y 0)) (Nat.mul 32 (Nat.add (dig5 x (dig5 y 1)) (Nat.mul 32 (Nat.add (dig5 x
  (dig5 y 2)) (Nat.mul 32 (Nat.add (dig5 x (dig5 y 3)) (Nat.mul 32 (Nat.add (dig5 x (dig5 y 4))
  (Nat.mul 32 (Nat.add (dig5 x (dig5 y 5)) (Nat.mul 32 (Nat.add (dig5 x (dig5 y 6)) (Nat.mul 32
  (Nat.add (dig5 x (dig5 y 7)) (Nat.mul 32 (Nat.add (dig5 x (dig5 y 8)) (Nat.mul 32 (Nat.add (dig5 x
  (dig5 y 9)) (Nat.mul 32 (Nat.add (dig5 x (dig5 y 10)) (Nat.mul 32 (Nat.add (dig5 x (dig5 y 11))
  (Nat.mul 32 (Nat.add (dig5 x (dig5 y 12)) (Nat.mul 32 (Nat.add (dig5 x (dig5 y 13)) (Nat.mul 32
  (Nat.add (dig5 x (dig5 y 14)) (Nat.mul 32 (Nat.add (dig5 x (dig5 y 15)) (Nat.mul 32 (Nat.add (dig5
  x (dig5 y 16)) (Nat.mul 32 (Nat.add (dig5 x (dig5 y 17)) (Nat.mul 32 (Nat.add (dig5 x (dig5 y 18))
  (Nat.mul 32 (Nat.add (dig5 x (dig5 y 19)) (Nat.mul 32 (Nat.add (dig5 x (dig5 y 20)) (Nat.mul 32
  (Nat.add (dig5 x (dig5 y 21)) (Nat.mul 32 (Nat.add (dig5 x (dig5 y 22)) (Nat.mul 32
  0)))))))))))))))))))))))))))))))))))))))))))))

theorem mul23_eq (x y : ℕ) :
    mul23 x y = ofDigs (2 ^ 5) (List.ofFn fun k : Fin 23 => digW 5 x (digW 5 y k)) := by
  simp only [List.ofFn_succ, List.ofFn_zero, ofDigs]
  rfl

theorem permCode_mul23 (σ τ : Perm (Fin 23)) :
    permCode (σ * τ) = mul23 (permCode σ) (permCode τ) := by
  rw [mul23_eq]
  have key : ∀ k : Fin 23, digW 5 (permCode σ) (digW 5 (permCode τ) k) = ((σ * τ) k : ℕ) := by
    intro k
    rw [digW_permCode (by norm_num) τ k, digW_permCode (by norm_num) σ (τ k)]
    rfl
  simp only [key]
  rfl

@[expose] def powC23 (one : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => one
  | k + 1, x => mul23 (powC23 one k x) x

theorem permCode_pow23 (σ : Perm (Fin 23)) (k : ℕ) :
    permCode (σ ^ k) = powC23 (permCode (1 : Perm (Fin 23))) k (permCode σ) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ, permCode_mul23, ih, powC23]

@[expose] def sqC23 : ℕ → ℕ → ℕ
  | 0, x => x
  | k + 1, x => sqC23 k (mul23 x x)

theorem permCode_pow_two_pow23 (k : ℕ) : ∀ σ : Perm (Fin 23),
    permCode (σ ^ 2 ^ k) = sqC23 k (permCode σ) := by
  induction k with
  | zero => intro σ; rw [pow_zero, pow_one]; rfl
  | succ k ih =>
    intro σ
    rw [pow_succ', pow_mul, sq, ih, permCode_mul23]
    rfl

theorem eq_of_permCode23 {σ τ : Perm (Fin 23)} (h : permCode σ = permCode τ) : σ = τ :=
  permCode_injective (by norm_num) h

end CFSG.Quasithin.F134
