module

public section

namespace CFSG.KC.ClosK

@[expose] def insK (pc : Nat → Nat → Nat) (gs : Nat → Nat) (g : Nat) (L : List Nat) (k : Nat) :
    List Nat :=
  cond (L.any fun x => Nat.beq x (pc (gs k) g)) L (L ++ [pc (gs k) g])

@[expose] def stepK (pc : Nat → Nat → Nat) (gs : Nat → Nat) (ng : Nat) (s : List Nat × Nat) :
    List Nat × Nat :=
  cond (Nat.blt s.2 s.1.length)
    ((List.range ng).foldl (insK pc gs (s.1.getD s.2 0)) s.1, s.2 + 1) s

@[expose] def closK (pc : Nat → Nat → Nat) (gs : Nat → Nat) (ng : Nat) :
    Nat → List Nat × Nat → List Nat × Nat
  | 0, s => s
  | c + 1, s => stepK pc gs ng (closK pc gs ng c s)

@[expose] def lEq (f : Nat → Nat) : List Nat → Nat → Nat → Bool
  | [], j, m => Nat.beq j m
  | x :: xs, j, m => cond (Nat.beq x (f j)) (lEq f xs (j + 1) m) false

end CFSG.KC.ClosK

end
