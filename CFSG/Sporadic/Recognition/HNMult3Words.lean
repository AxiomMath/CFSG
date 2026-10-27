module

public import CFSG.Sporadic.Recognition.CoverRecipeCube

public section

namespace CFSG.Sporadic.Recognition.HNMult3

open CFSG.LieType.Multipliers CFSG.Sporadic.Recognition.CoverRecipe

@[expose] def ofCodes3 (c : List ℕ) : List (Fin 3 × Bool) :=
  c.map (fun x => (⟨x / 2 % 3, Nat.mod_lt _ (by norm_num)⟩, decide (x % 2 = 0)))

@[expose] def hn3RelCodes : List (List ℕ) :=
  [[4, 4],
   [0, 0, 0],
   [2, 0, 2, 0, 2, 0],
   [2, 4, 3, 1, 2, 4, 3, 1],
   [3, 3, 4, 1, 4, 2, 4, 1, 4, 3, 3],
   [0, 2, 0, 3, 4, 3, 3, 1, 3, 3, 4, 3],
   [2, 2, 4, 0, 3, 4, 2, 2, 4, 0, 3, 4],
   [0, 4, 2, 1, 4, 3, 3, 1, 4, 2, 1, 4, 3, 3],
   [4, 0, 2, 1, 4, 3, 1, 3, 3, 1, 4, 3, 1, 4, 0],
   [4, 3, 1, 3, 4, 0, 2, 1, 3, 1, 4, 3, 1, 4, 1],
   [3, 3, 4, 0, 2, 2, 1, 3, 3, 4, 1, 4, 0, 3, 1, 4, 1],
   [4, 0, 2, 4, 0, 2, 4, 0, 2, 4, 0, 2, 4, 0, 2, 4, 0, 2]]

@[expose] def hn3Rels : List (List (Fin 3 × Bool)) := hn3RelCodes.map ofCodes3

@[expose] def hn3CommCodes : List (List (List ℕ × List ℕ)) :=
  [[([1], [2, 4, 3])],
   [([0, 3, 1], [1, 4, 1, 2])],
   []]

@[expose] def hn3Comm (i : Fin 3) : List (List (Fin 3 × Bool) × List (Fin 3 × Bool)) :=
  (hn3CommCodes.getD i.val []).map fun p => (ofCodes3 p.1, ofCodes3 p.2)

@[expose] def hn3Ord : Fin 3 → ℕ := ![0, 0, 2]

@[expose] def hn3Cw (i : Fin 3) : List (Fin 3 × Bool) :=
  if hn3Ord i = 0 then commWords (hn3Comm i) else [(i, true)]

@[expose] def hn3Cover : List (List (Fin 3 × Bool)) := cover₃Words hn3Rels hn3Cw hn3Ord

end CFSG.Sporadic.Recognition.HNMult3

end
