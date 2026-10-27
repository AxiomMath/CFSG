module

public import CFSG.Monster.B.TwoA.Unitary.WStab
public import CFSG.Monster.B.Rep4371.Bits
public import CFSG.Monster.VisCert.Basis
public meta import CFSG.Monster.B.Rep4371.Model
public meta import CFSG.Monster.B.TwoA.Unitary.NData
public meta import CFSG.Monster.B.TwoA.Unitary.WStab

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.GSide

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Unitary
open CFSG.Monster.B.Rep4371 (RepPerm permWord_bvec)

@[expose] def p2Gen (k : Fin 6) : P2 := ⟨n6Aut k, n6Aut_mem_P2 k⟩

@[expose] def p2Word : List (Fin 6) → P2
  | [] => 1
  | k :: w => p2Word w * p2Gen k

@[expose] def arrMul (p q : Array ℕ) : Array ℕ := Array.ofFn fun i : Fin 24 => p[q[(i : ℕ)]!]!

@[expose] def arrId : Array ℕ := Array.ofFn fun i : Fin 24 => (i : ℕ)

@[expose] def p2Arr : List (Fin 6) → Array ℕ
  | [] => arrId
  | k :: w => arrMul (p2Arr w) n6PermArr[(k : ℕ)]!

@[expose] def deltaPaths : List (List (Fin 6)) :=
  [[], [4], [4, 1], [4, 1, 0], [4, 1, 2], [4, 3], [4, 1, 3], [4, 3, 1], [4, 1, 2, 3],
    [4, 3, 0, 1], [4, 1, 3, 0, 0], [4, 3, 0, 3], [4, 3, 0, 0], [4, 3, 3], [4, 1, 3, 0],
    [4, 3, 0], [4, 3, 1, 0], [4, 3, 0, 2], [4, 3, 1, 4], [4, 1, 3, 0, 2], [4, 3, 3, 5]]

@[expose] def coeffStep (c : Fin 10 → ZMod 2) (m : ℕ) (i : Fin 10) : ℕ :=
  if c i = 1 then m ^^^ signMask i else m

@[expose] def coeffMask (c : Fin 10 → ZMod 2) : ℕ := (List.finRange 10).foldl (coeffStep c) 0

@[expose] def wordA : List (Fin 6) := [1, 1, 4, 3, 1, 3, 0]

@[expose] def wordB : List (Fin 6) := [0, 0, 2, 2, 4, 0, 3]

@[expose] def vStar : ℕ := 1589783

end CFSG.Monster.B.GSide
