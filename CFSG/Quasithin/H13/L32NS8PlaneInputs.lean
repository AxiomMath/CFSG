module

public import CFSG.Quasithin.H13.L32NS8Inputs

public section

namespace CFSG.Quasithin.H13.S8Cert

open Mat8Cert

@[expose] def t8W : List (List ℕ) := [[2], [3], [4, 2, 0, 4, 2, 0, 4, 2, 0]]

@[expose] def t8G : List (List ℕ) := t8W.map (evalW s8G)

@[expose] def t8E : List (List ℕ) := elemsOf t8G

@[expose] def t8BasicB : Bool := subB t8G t8E && t8E.length == 128

@[expose] def t8FixB : Bool :=
  (List.range 256).filter (fun v => t8G.all fun t => mv8 t v == v) == [0, vR]

@[expose] def t8PlaneB : Bool :=
  (List.range 256).all fun a => a == 0 || a == vR ||
    !(t8G.all fun t => mv8 t a == a || mv8 t a == (a ^^^ vR)) || (inII a && inII (a ^^^ vR))

@[expose] def s8IIB : Bool :=
  s8G.all fun g => (List.range 256).all fun v => inII (mv8 g v) == inII v

@[expose] def tvCols (i j : ℕ) : List ℕ :=
  (List.range 8).map fun k =>
    if k == j then 2 ^ j + 2 ^ i else if k == 4 + i then 2 ^ (4 + i) + 2 ^ (4 + j) else 2 ^ k

@[expose] def tvW : List (ℕ × ℕ × List ℕ) :=
  [(0, 1, [0]), (0, 2, [1, 0, 1, 0]), (0, 3, [4, 3, 4]), (1, 0, [4, 0, 4]), (1, 2, [1]),
    (1, 3, [2, 1, 2, 1]), (2, 0, [3, 2, 3, 2]), (2, 1, [4, 1, 4]), (2, 3, [2]), (3, 0, [3]),
    (3, 1, [3, 0, 3, 0]), (3, 2, [4, 2, 4])]

@[expose] def tvB : Bool := tvW.all fun p => evalW s8G p.2.2 == tvCols p.1 p.2.1

@[expose] def planeCheck : Bool := t8BasicB && t8FixB && t8PlaneB && s8IIB && tvB

end CFSG.Quasithin.H13.S8Cert
