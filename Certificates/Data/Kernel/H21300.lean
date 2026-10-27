module

public import CFSG.Holt.SmallGroupsCheck
public import Mathlib.GroupTheory.Perm.Fin

public section

namespace CFSG.KD.H21300

@[expose] def permsOf : Nat → List Nat → List (List Nat)
  | 0, _ => [[]]
  | k + 1, avail => avail.flatMap fun a => (permsOf k (avail.erase a)).map (a :: ·)

@[expose] def fx (l : List Nat) (k : Nat) : Nat := if l.getD k 0 = k then 1 else 0

@[expose] def mv (l : List Nat) (k : Nat) : Nat := if l.getD k 0 = k then 0 else 1

@[expose] def fix (l : List Nat) : Nat :=
  fx l 0 + fx l 1 + fx l 2 + fx l 3 + fx l 4 + fx l 5 + fx l 6

@[expose] def cnt (l : List Nat) : Nat :=
  mv l 0 + mv l 1 + mv l 2 + mv l 3 + mv l 4 + mv l 5 + mv l 6

@[expose] def invB (l : List Nat) : Bool :=
  (List.range 7).all fun i => l.getD (l.getD i 0) 0 == i

@[expose] def inv3 (l : List Nat) : Bool := invB l && fix l == 3

@[expose] def inv0 (l : List Nat) : Bool := invB l && fix l == 1 && l.getD 0 0 == 0

@[expose] def LUs : List (List Nat) := (permsOf 7 (List.range 7)).filter inv3

@[expose] def LTs : List (List Nat) := (permsOf 7 (List.range 7)).filter inv0

@[expose] def gen (a b : List Nat) (k : Fin 3) : List Nat :=
  if k.val = 0 then [1, 2, 3, 4, 5, 6, 0] else if k.val = 1 then a else b

@[expose] def step (g x : List Nat) : List Nat := x.map fun j => g.getD j 0

@[expose] def evalL (a b : List Nat) (w : List (Fin 3)) : List Nat :=
  w.foldl (fun x k => step (gen a b k) x) [0, 1, 2, 3, 4, 5, 6]

@[expose] def pack (l : List Nat) : Nat :=
  l.getD 0 0 + (l.getD 1 0 <<< 3) + (l.getD 2 0 <<< 6) + (l.getD 3 0 <<< 9) +
    (l.getD 4 0 <<< 12) + (l.getD 5 0 <<< 15) + (l.getD 6 0 <<< 18)

@[expose] def decode (c : Nat) : List Nat :=
  [c &&& 7, (c >>> 3) &&& 7, (c >>> 6) &&& 7, (c >>> 9) &&& 7, (c >>> 12) &&& 7,
    (c >>> 15) &&& 7, (c >>> 18) &&& 7]

@[expose] def covB (L : List (List Nat)) (A : List Nat) : Bool :=
  L.all fun a => A.any fun c => decode c == a

@[expose] def rowH (c : Nat) : List Nat → Nat → Bool
  | [], _ => true
  | d :: B, h => cnt (evalL (decode c) (decode d)
      (CFSG.Holt.SmallGroups.s7Words.getD (h % 64) [])) == 2 && rowH c B (h / 64)

@[expose] def chkH (B : List Nat) : List Nat → List Nat → Bool
  | [], _ => true
  | _ :: _, [] => false
  | c :: A, h :: H => rowH c B h && chkH B A H

end CFSG.KD.H21300

end
