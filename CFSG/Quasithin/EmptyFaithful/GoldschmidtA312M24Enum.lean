
module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicBase

public section

namespace CFSG.Quasithin.A312M24

open CFSG.QuasithinUnique.K1.SporadicPerm

@[expose] def bfsAdd (Gt : List (List ℕ)) (i : ℕ) (st : List (List ℕ) × List (ℕ × ℕ)) :
    List (List ℕ) × List (ℕ × ℕ) :=
  (List.range Gt.length).foldl (fun acc s =>
    let t := compTab (st.1.getD i []) (Gt.getD s [])
    if acc.1.contains t then acc else (acc.1 ++ [t], acc.2 ++ [(i, s)])) st

@[expose] def bfsLoop (Gt : List (List ℕ)) : ℕ → ℕ → List (List ℕ) × List (ℕ × ℕ) →
    List (List ℕ) × List (ℕ × ℕ)
  | 0, _, st => st
  | fuel + 1, i, st => if i < st.1.length then bfsLoop Gt fuel (i + 1) (bfsAdd Gt i st) else st

@[expose] def bfsL (n : ℕ) (Gt : List (List ℕ)) (fuel : ℕ) : List (List ℕ) × List (ℕ × ℕ) :=
  bfsLoop Gt fuel 0 ([List.range n], [(0, 0)])

end CFSG.Quasithin.A312M24
