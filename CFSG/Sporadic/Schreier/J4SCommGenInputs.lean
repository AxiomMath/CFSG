
module

public import CFSG.Sporadic.Schreier.J4SLocalNodesBase
public import CFSG.Sporadic.Schreier.J4SNative
public import CFSG.Sporadic.Schreier.J4SCols
public import CFSG.Sporadic.Schreier.J4SOrbitsBase
public meta import CFSG.Sporadic.Schreier.J4SOrbitsBase

public noncomputable section

namespace CFSG.Sporadic.J4Schreier

open CFSG.Sporadic.J4 CFSG.Sporadic.SmallF2.Native MulAction

section Generic

variable {G : Type*} [Group G]

@[expose] def xorSub : List ℕ → ℕ → ℕ
  | [], _ => 0
  | w :: ws, m => (if m % 2 = 1 then w else 0) ^^^ xorSub ws (m / 2)

end Generic

@[expose] def commPicks : List (ℕ × ℕ) :=
  [(1, 0), (2, 0), (4, 0), (5, 0), (8, 0), (10, 0), (1, 1), (2, 1), (3, 1), (5, 1), (4, 5)]

@[expose] def commVec (p : ℕ × ℕ) : ℕ := 2 ^ p.1 ^^^ app11 gens1[p.2]! (2 ^ p.1)

end CFSG.Sporadic.J4Schreier
