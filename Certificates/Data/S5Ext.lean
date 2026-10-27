module

public section

namespace CFSG.CGT.PushingUpLit.SolK.S5Ext

@[expose] def pmulN (i j : Nat) : Nat :=
  (i ^^^ j) ^^^ ((((i >>> 3) &&& (j >>> 1) &&& 1) ^^^ ((i >>> 4) &&& j &&& 1)) <<< 2)

@[expose] def pmul (i j : Fin 32) : Fin 32 :=
  ⟨pmulN i.val j.val % 32, Nat.mod_lt _ (by decide)⟩

@[expose] def pgen (k : Nat) : Fin 32 :=
  if k = 0 then 1 else if k = 1 then 2 else if k = 2 then 8 else 16

@[expose] def pwordTab : Array (List Nat) :=
  #[[], [0], [1], [0, 1], [0, 3, 0, 3], [3, 0, 3], [2, 1, 2], [0, 2, 1, 2], [2], [0, 2], [1, 2],
    [0, 1, 2], [1, 2, 1], [0, 1, 2, 1], [2, 1], [0, 2, 1], [3], [0, 3], [1, 3], [0, 1, 3],
    [0, 3, 0], [3, 0], [0, 1, 3, 0], [1, 3, 0], [2, 3], [0, 2, 3], [1, 2, 3], [0, 1, 2, 3],
    [0, 2, 3, 0], [2, 3, 0], [2, 1, 3], [0, 2, 1, 3]]

@[expose] def pword (i : Fin 32) : List Nat := pwordTab.getD i.val []

@[expose] def evalW (g : Nat → Fin 32) (w : List Nat) : Fin 32 :=
  w.foldl (fun acc k => pmul acc (g k)) 0

@[expose] def gens4 (a b c d : Fin 32) (k : Nat) : Fin 32 :=
  if k = 0 then a else if k = 1 then b else if k = 2 then c else d

end CFSG.CGT.PushingUpLit.SolK.S5Ext

