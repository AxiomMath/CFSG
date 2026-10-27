module

public import Init

public section

namespace CFSG.KC.Fi22U

@[expose] def co (c i : Nat) : Nat := c / 4 ^ i % 4

@[expose] def addC (a b : Nat) : Nat := (a % 4) ^^^ (b % 4)

@[expose] def mulC (a b : Nat) : Nat :=
  (a % 4 % 2 * (b % 4 % 2) + a % 4 / 2 * (b % 4 / 2)) % 2 +
    2 * ((a % 4 % 2 * (b % 4 / 2) + a % 4 / 2 * (b % 4 % 2) + a % 4 / 2 * (b % 4 / 2)) % 2)

@[expose] def mk6 (a b c d e f : Nat) : Nat := a + 4 * (b + 4 * (c + 4 * (d + 4 * (e + 4 * f))))

@[expose] def scaleC (s c : Nat) : Nat :=
  mk6 (mulC s (co c 0)) (mulC s (co c 1)) (mulC s (co c 2)) (mulC s (co c 3)) (mulC s (co c 4))
    (mulC s (co c 5))

@[expose] def addV (x y : Nat) : Nat :=
  mk6 (addC (co x 0) (co y 0)) (addC (co x 1) (co y 1)) (addC (co x 2) (co y 2))
    (addC (co x 3) (co y 3)) (addC (co x 4) (co y 4)) (addC (co x 5) (co y 5))

@[expose] def hT (v x i : Nat) : Nat := mulC (mulC (co v i) (co v i)) (co x i)

@[expose] def hermC (v x : Nat) : Nat :=
  addC (addC (addC (addC (addC (hT v x 0) (hT v x 1)) (hT v x 2)) (hT v x 3)) (hT v x 4))
    (hT v x 5)

@[expose] def tvC (v x : Nat) : Nat := addV x (scaleC (hermC v x) v)

@[expose] def normC (c : Nat) : Nat :=
  if co c 0 ≠ 0 then scaleC (mulC (co c 0) (co c 0)) c
  else if co c 1 ≠ 0 then scaleC (mulC (co c 1) (co c 1)) c
  else if co c 2 ≠ 0 then scaleC (mulC (co c 2) (co c 2)) c
  else if co c 3 ≠ 0 then scaleC (mulC (co c 3) (co c 3)) c
  else if co c 4 ≠ 0 then scaleC (mulC (co c 4) (co c 4)) c
  else if co c 5 ≠ 0 then scaleC (mulC (co c 5) (co c 5)) c
  else c

@[expose] def lexFrom (a b : Nat) : Nat → Bool
  | 0 => decide (co a 5 < co b 5)
  | k + 1 => decide (co a (4 - k) < co b (4 - k)) ||
      (decide (co a (4 - k) = co b (4 - k)) && lexFrom a b k)

@[expose] def lexC (a b : Nat) : Bool := lexFrom a b 5

@[expose] def ptOK (c : Nat) : Bool := !(c == 0) && hermC c c == 0 && normC c == c

@[expose] def tabC (T k : Nat) : Nat := T / 4 ^ (6 * k) % 4096

@[expose] def charsC : List Char → Nat
  | [] => 0
  | c :: cs => (c.toNat - 48) + 4 * charsC cs

@[expose] def cntPt : Nat → Nat
  | 0 => 0
  | n + 1 => cntPt n + if ptOK n then 1 else 0

end CFSG.KC.Fi22U

end
