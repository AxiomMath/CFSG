module

public import Certificates.Data.CFSGNative.KGroups.Perm

public section

namespace CFSG.Quasithin.Asc81c.Pf.Check

open CFSG.Monster.B.Co2.Native CFSG.KGroups.Native

@[expose] def linV (n : Nat) (c : List Nat) (i : Nat) : Nat :=
  (List.range n).foldl (fun acc k => if i.testBit k then acc ^^^ c.getD k 0 else acc) 0

@[expose] def linA (n : Nat) (c : List Nat) : Array Nat :=
  Array.ofFn (n := 2 ^ n) fun i => linV n c i.val

@[expose] def x0c (n : Nat) : List Nat := 2 :: 3 :: (List.range (n - 2)).map fun k => 2 ^ (k + 2)

@[expose] def x0 (n : Nat) : Array Nat := linA n (x0c n)

@[expose] def ord3V (n : Nat) (c : List Nat) : Bool :=
  (List.range n).all fun k => linV n c (linV n c (linV n c (2 ^ k))) == 2 ^ k

@[expose] def ord3A (N : Nat) (t : Array Nat) : Bool := eqA N (powA N t 3) (idA N)

@[expose] def fixCount (N : Nat) (t : Array Nat) : Nat :=
  ((List.finRange N).filter fun i => t[i.val]! == i.val).length

@[expose] def meetTriv (N : Nat) (x t : Array Nat) : Bool :=
  allLt N fun i => !(x[i]! == i && t[i]! == i) || i == 0

@[expose] def fixL (N : Nat) (t₁ t₂ : Array Nat) : List Nat :=
  (List.range N).filter fun i => t₁[i]! == i && t₂[i]! == i

@[expose] def sumL (N : Nat) (D : List Nat) (u : Array Nat) : List Nat :=
  D.flatMap fun d => (List.range N).map fun i => d ^^^ i ^^^ u[i]!

@[expose] def bigEnough (n : Nat) (P : List Nat) : Bool :=
  if n = 3 then P.any fun p => p != 0
  else P.any fun p => p != 0 && P.any fun q => q != 0 && q != p

@[expose] def critA (n : Nat) (t₁ t₂ u : Array Nat) : Bool :=
  isInvolA (2 ^ n) u && ord3A (2 ^ n) t₁ && ord3A (2 ^ n) t₂ &&
    bigEnough n (sumL (2 ^ n) (fixL (2 ^ n) t₁ t₂) u)

@[expose] def wordsOfLen : Nat → List (List Bool)
  | 0 => [[]]
  | L + 1 => (wordsOfLen L).flatMap fun w => [false :: w, true :: w]

@[expose] def wordsUpTo (L : Nat) : List (List Bool) := (List.range (L + 1)).flatMap wordsOfLen

@[expose] def plainOK (n : Nat) (x t : Array Nat) : Bool :=
  (wordsUpTo 10).any fun w => critA n x t (evalWA (2 ^ n) x t w)

@[expose] def genOK (n : Nat) (x t : Array Nat) : Bool :=
  (wordsUpTo 4).any fun w₁ =>
    let t₁ := evalWA (2 ^ n) x t w₁
    ord3A (2 ^ n) t₁ && (wordsUpTo 4).any fun w₂ =>
      let t₂ := evalWA (2 ^ n) x t w₂
      ord3A (2 ^ n) t₂ && decide (2 ≤ (fixL (2 ^ n) t₁ t₂).length) &&
        (wordsUpTo 4).any fun w => critA n t₁ t₂ (evalWA (2 ^ n) t₁ t₂ w)

@[expose] def closureW (N : Nat) (a b : Array Nat) : Nat → List (List Bool) → List (List Bool)
  | 0, acc => acc
  | fuel + 1, acc =>
    let new := acc.foldl (fun l w => [w ++ [false], w ++ [true]].foldl (fun l' w' =>
      if l'.any fun v => eqA N (evalWA N a b v) (evalWA N a b w') then l' else l' ++ [w']) l) acc
    if new.length == acc.length then acc else closureW N a b fuel new

@[expose] def pairwiseNe (N : Nat) : List (Array Nat) → Bool
  | [] => true
  | s :: L => (L.all fun t => !eqA N s t) && pairwiseNe N L

@[expose] def closedOK (N : Nat) (a b : Array Nat) (l : List (List Bool)) : Bool :=
  l.length == 21 && pairwiseNe N (l.map (evalWA N a b)) && l.contains [] &&
    l.all fun w => (l.any fun w' => eqA N (evalWA N a b (w ++ [false])) (evalWA N a b w')) &&
      (l.any fun w' => eqA N (evalWA N a b (w ++ [true])) (evalWA N a b w'))

@[expose] def f21OK (n : Nat) (x t : Array Nat) : Bool :=
  closedOK (2 ^ n) x t (closureW (2 ^ n) x t 25 [[]])

@[expose] def pairOK (n : Nat) (x : Array Nat) (c : List Nat) : Bool :=
  !ord3V n c ||
    let t := linA n c
    !(fixCount (2 ^ n) t == 2 ^ (n - 2) && meetTriv (2 ^ n) x t) ||
      eqA (2 ^ n) (compA (2 ^ n) x t) (compA (2 ^ n) t x) || plainOK n x t || genOK n x t ||
      (n == 3 && f21OK n x t)

@[expose] def check4 : Bool :=
  allLt 16 fun a => allLt 16 fun b => allLt 16 fun c => allLt 16 fun d =>
    pairOK 4 (x0 4) [a, b, c, d]

@[expose] def check3 : Bool :=
  allLt 8 fun a => allLt 8 fun b => allLt 8 fun c => pairOK 3 (x0 3) [a, b, c]

end CFSG.Quasithin.Asc81c.Pf.Check
