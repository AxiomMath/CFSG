module

public import CFSG.Monster.B.E6.StdF4RadicalGroup

public noncomputable section

namespace CFSG.Monster.B.E6.StdF4Radical

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Std
open CFSG.LieType.Chevalley.C2E6Overlap CFSG.Monster.B.E6.StdF4
open CFSG.LieType.Chevalley.C2E6Std.FieldExtension
open scoped commutatorElement

abbrev ei (i : Fin Tag.E6.rank) : Fin Tag.E6.rank → ℤ := Pi.single i 1

@[expose] def levRoot (c : ℕ) : Fin Tag.E6.rank → ℤ :=
  [ei 3, -ei 3, ei 2, ei 4, -ei 2, -ei 4, ei 0, ei 5, -ei 0, -ei 5].getD c 0

@[expose] def levAdd (c k : ℕ) : ℕ :=
  ([[1, 21, 21, 21, 21, 21, 9, 10, 11, 21, 21, 21, 21, 21, 15, 21, 21, 21, 19, 21, 21],
    [21, 0, 21, 21, 21, 21, 21, 21, 21, 6, 7, 8, 21, 21, 21, 14, 21, 21, 21, 18, 21],
    [21, 3, 6, 21, 7, 21, 21, 21, 21, 21, 21, 13, 21, 21, 21, 17, 18, 21, 21, 21, 21],
    [21, 2, 21, 6, 21, 8, 21, 21, 21, 21, 12, 21, 21, 21, 21, 16, 21, 18, 21, 21, 21],
    [21, 21, 21, 1, 21, 21, 2, 4, 21, 21, 21, 21, 21, 11, 21, 21, 21, 15, 16, 21, 21],
    [21, 21, 1, 21, 21, 21, 3, 21, 5, 21, 21, 21, 10, 21, 21, 21, 15, 21, 17, 21, 21],
    [21, 21, 21, 5, 21, 21, 8, 14, 21, 11, 15, 21, 16, 21, 21, 21, 21, 21, 21, 21, 21],
    [21, 21, 4, 21, 21, 21, 7, 21, 14, 10, 21, 15, 21, 17, 21, 21, 21, 21, 21, 21, 21],
    [21, 21, 21, 21, 21, 3, 21, 21, 6, 21, 21, 9, 21, 21, 7, 10, 12, 21, 21, 21, 21],
    [21, 21, 21, 21, 2, 21, 21, 6, 21, 21, 9, 21, 21, 21, 8, 11, 21, 13, 21, 21, 21]].getD c
    []).getD k 21

@[expose] def conjW (c k : ℕ) : List ℕ := if levAdd c k < 21 then [levAdd c k, k] else [k]

@[expose] def leviConjW (k : ℕ) (w : List ℕ) : List ℕ :=
  match k with
  | 0 => w.flatMap (conjW 0)
  | 1 => w.flatMap (conjW 1)
  | 2 => (w.flatMap (conjW 3)).flatMap (conjW 2)
  | 3 => (w.flatMap (conjW 5)).flatMap (conjW 4)
  | 4 => (w.flatMap (conjW 7)).flatMap (conjW 6)
  | _ => (w.flatMap (conjW 9)).flatMap (conjW 8)

@[expose] def inQMask (m : ℕ) : Bool :=
  (List.range 15).all fun i => (orbIdx i).all fun k => m.testBit k == m.testBit ((orbIdx i).headD 0)

@[expose] def centerCols : Fin 6 → Fin 7 → ℕ :=
  ![![1, 2, 4, 25, 16, 32, 64], ![1, 2, 4, 8, 25, 32, 64], ![1, 2, 12, 8, 48, 32, 64],
    ![1, 2, 4, 12, 16, 48, 64], ![1, 6, 4, 8, 16, 96, 64], ![1, 2, 6, 8, 16, 32, 96]]

@[expose] def zWordOf (m : ℕ) : List ℕ :=
  (List.range 7).flatMap fun j => if m.testBit j then orbIdx (zIdx j) else []

end CFSG.Monster.B.E6.StdF4Radical
