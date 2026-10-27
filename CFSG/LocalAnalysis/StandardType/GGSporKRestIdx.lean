module

public import Aesop.BuiltinRules
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.ToDual

public section

namespace CFSG.StandardType.SporadicShape

@[expose] def sporKRestMulIdx (mul : List (List ℕ)) (a b : ℕ) : ℕ :=
  (mul.getD a []).getD b 0

@[expose] def sporKRestPowIdx (mul : List (List ℕ)) (a : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => sporKRestMulIdx mul (sporKRestPowIdx mul a k) a

@[expose] def sporKRestECond (n p : ℕ) (mul : List (List ℕ)) (good : List Bool) : Bool :=
  (List.range n).all fun a => (List.range n).all fun b =>
    !(decide (a ≠ 0) && decide (b ≠ 0) &&
      decide (sporKRestMulIdx mul a b = sporKRestMulIdx mul b a) &&
      decide (sporKRestPowIdx mul a p = 0) && decide (sporKRestPowIdx mul b p = 0) &&
      (List.range p).all fun i => decide (sporKRestPowIdx mul a i ≠ b)) ||
    (List.range p).any fun i => (List.range p).any fun j =>
      good.getD (sporKRestMulIdx mul (sporKRestPowIdx mul a i) (sporKRestPowIdx mul b j)) false

end CFSG.StandardType.SporadicShape
