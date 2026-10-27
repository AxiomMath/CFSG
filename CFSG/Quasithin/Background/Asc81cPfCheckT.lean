module

public import CFSG.Quasithin.Background.Asc81cPfCheck

public section

namespace CFSG.Quasithin.Asc81c.Pf.Check

open CFSG.Monster.B.Co2.Native CFSG.KGroups.Native

@[expose] def allLists (N : Nat) : Nat → List (List Nat)
  | 0 => [[]]
  | k + 1 => (List.range N).flatMap fun a => (allLists N k).map (a :: ·)

@[expose] def ord21A (N : Nat) (t : Array Nat) : Bool := eqA N (powA N t 21) (idA N)

@[expose] def lawsOK (n : Nat) (x t : Array Nat) : Bool :=
  (wordsUpTo 4).all fun w => ord21A (2 ^ n) (evalWA (2 ^ n) x t w)

@[expose] def pre1 (n : Nat) (x t : Array Nat) : Bool :=
  ord3A (2 ^ n) t && fixCount (2 ^ n) t == 2 ^ (n - 2) &&
    !eqA (2 ^ n) (compA (2 ^ n) x t) (compA (2 ^ n) t x) && lawsOK n x t

@[expose] def partners (n : Nat) (x : Array Nat) : List (Array Nat) :=
  (allLists (2 ^ n) n).filterMap fun c =>
    if ord3V n c then (if pre1 n x (linA n c) then some (linA n c) else none) else none

@[expose] def meet3 (N : Nat) (x a b : Array Nat) : Bool :=
  allLt N fun i => !(x[i]! == i && a[i]! == i && b[i]! == i) || i == 0

@[expose] def sameOK (N : Nat) (x a b : Array Nat) : Bool :=
  (wordsUpTo 6).any fun w => eqA N (evalWA N x a w) b

@[expose] def conjA (N : Nat) (c x : Array Nat) : Array Nat := compA N c (compA N x (powA N c 20))

@[expose] def ptOK (N : Nat) (x a b : Array Nat) : Bool :=
  (wordsUpTo 2).any fun w₁ =>
    let c₁ := evalWA N x a w₁
    ord21A N c₁ && (wordsUpTo 2).any fun w₂ =>
      let c₂ := evalWA N x b w₂
      ord21A N c₂ &&
        !eqA N (compA N (conjA N c₁ x) (conjA N c₂ x)) (compA N (conjA N c₂ x) (conjA N c₁ x)) &&
        (wordsUpTo 2).any fun v => !ord21A N (evalWA N (conjA N c₁ x) (conjA N c₂ x) v)

@[expose] def checkT (n : Nat) : Bool :=
  let x := x0 n
  let L := partners n x
  L.all fun a => L.all fun b => !meet3 (2 ^ n) x a b || ptOK (2 ^ n) x a b || sameOK (2 ^ n) x a b

end CFSG.Quasithin.Asc81c.Pf.Check
