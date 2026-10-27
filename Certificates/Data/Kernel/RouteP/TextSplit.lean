module

public import Init

public section

namespace CFSG.KC.RouteP

@[expose] def splitSL (cs sep : List Char) (n : Nat) :
    Nat → Nat → Nat → Nat → List (List Char) → List (List Char)
  | 0, _, _, _, r => r.reverse
  | f + 1, b, i, j, r =>
    if n ≤ i then (((cs.drop b).take (i - b)) :: r).reverse
    else if cs.getD i 'a' == sep.getD j 'a' then
      if sep.length ≤ j + 1 then splitSL cs sep n f (i + 1) (i + 1) 0 ((cs.drop b).take (i - j - b) :: r)
      else splitSL cs sep n f b (i + 1) (j + 1) r
    else splitSL cs sep n f b (i - j + 1) 0 r

@[expose] def splitSepL (cs sep : List Char) : List (List Char) :=
  splitSL cs sep cs.length ((cs.length + 2) * (sep.length + 1) + 1) 0 0 0 []

end CFSG.KC.RouteP
