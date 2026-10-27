module

public import CFSG.Open.StatedDefs
public import Mathlib.LinearAlgebra.BilinearMap

public section

namespace CFSG.RankThree.GF2n.Stroth80.Tri

open CFSG.Open

variable {K : Type*} [CommRing K]

abbrev Oct (K : Type*) := Fin 4 ⊕ Fin 4 → K

@[expose] def octA (x : Oct K) : K := x (.inl 0)

@[expose] def octB (x : Oct K) : K := x (.inr 0)

@[expose] def octU (x : Oct K) (i : Fin 3) : K := x (.inl i.succ)

@[expose] def octW (x : Oct K) (i : Fin 3) : K := x (.inr i.succ)

@[expose] def dot3 (u w : Fin 3 → K) : K := u 0 * w 0 + u 1 * w 1 + u 2 * w 2

@[expose] def cross3 (u w : Fin 3 → K) : Fin 3 → K :=
  ![u 1 * w 2 - u 2 * w 1, u 2 * w 0 - u 0 * w 2, u 0 * w 1 - u 1 * w 0]

@[expose] def octMk (a : K) (u w : Fin 3 → K) (b : K) : Oct K
  | .inl i => Fin.cases a u i
  | .inr i => Fin.cases b w i

@[expose] def octMul (x y : Oct K) : Oct K :=
  octMk (octA x * octA y + dot3 (octU x) (octW y))
    (fun i => octA x * octU y i + octB y * octU x i - cross3 (octW x) (octW y) i)
    (fun i => octA y * octW x i + octB x * octW y i + cross3 (octU x) (octU y) i)
    (octB x * octB y + dot3 (octW x) (octU y))

@[expose] def octNorm (x : Oct K) : K := octA x * octB x - dot3 (octU x) (octW x)

@[expose] def octConj (x : Oct K) : Oct K := octMk (octB x) (-octU x) (-octW x) (octA x)

@[expose] def octOne : Oct K := octMk 1 0 0 1

end CFSG.RankThree.GF2n.Stroth80.Tri

end
