module

public import Mathlib.Algebra.Group.Defs

public section

namespace CFSG.KD.L5

@[expose] def wBfsRoundG {G : Type*} [Mul G] [BEq G] (gens : List G) (tab : List (G × List ℕ)) :
    List (G × List ℕ) :=
  tab.foldl (fun acc pw => (gens.mapIdx fun i g => (pw.1 * g, pw.2 ++ [i])).foldl
    (fun acc2 qw => if acc2.any (fun e => e.1 == qw.1) then acc2 else acc2 ++ [qw]) acc) tab

@[expose] def wBfsTabG {G : Type*} [Monoid G] [BEq G] (gens : List G) : ℕ → List (G × List ℕ)
  | 0 => [(1, [])]
  | n + 1 => wBfsRoundG gens (wBfsTabG gens n)

end CFSG.KD.L5

end
