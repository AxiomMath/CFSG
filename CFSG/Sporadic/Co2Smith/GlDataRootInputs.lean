module

public import CFSG.Sporadic.Co2Smith.GlDataInputs
public import CFSG.Sporadic.Co2Smith.GlDataRoots

public section

namespace CFSG.Sporadic.Co2Smith.Native

open CFSG.Sporadic.SmallF2.Native CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
  CFSG.Sporadic.Co2Cert

set_option compiler.extract_closed false

@[expose] def f4mul (s t : Nat) : Nat :=
  if s == 0 || t == 0 then 0 else ((s - 1 + (t - 1)) % 3) + 1

@[expose] def glGD : Array Nat := mulRows 22 glGa glD1h

@[expose] def glDG : Array Nat := mulRows 22 glD1h glGa

@[expose] def glX24R (t : Nat) : Array Nat :=
  mulRows 22 (mulRows 22 glGD (glR (glPosNF[1]!)[t]!)) glDG

@[expose] def glPosRows (i t : Nat) : Array Nat :=
  if t == 0 then idRows 22
  else if i < 4 then glR (glPosNF[i]!)[t]!
  else if i == 4 then glX24R t
  else glConj glW3 (glX24R t)

@[expose] def glLongRows (k : Nat) : Array Nat :=
  if k == 0 then glZ else if k == 1 then glX25 else if k == 2 then glX34
  else if k == 3 then glX61 else if k == 4 then glX52 else glX43

@[expose] def glRootRows (r t : Nat) : Array Nat :=
  if t == 0 then idRows 22
  else if r < 6 then glPosRows r t
  else if r < 12 then glConj glW0 (glPosRows (r - 6) t)
  else glLongRows (r - 12)

@[expose] def glParams (r : Nat) : List Nat := if r < 12 then [1, 2, 3] else [1]

@[expose] def glOpp (a b : Nat) : Bool :=
  let ca := glRootCoord[a]!
  let cb := glRootCoord[b]!
  ca.1 == -cb.1 && ca.2.1 == -cb.2.1 && ca.2.2 == -cb.2.2

@[expose] def glCommLookup (a b s t : Nat) : List (Nat × Nat) :=
  ((glCommTable.find? fun e => e.1 == a && e.2.1 == b && e.2.2.1 == s && e.2.2.2.1 == t).map
    fun e => e.2.2.2.2).getD []

@[expose] def glProdRows (l : List (Nat × Nat)) : Array Nat :=
  l.foldr (fun p acc => mulRows 22 (glRootRows p.1 p.2) acc) (idRows 22)

@[expose] def glCommRows (X Y : Array Nat) : Array Nat :=
  mulRows 22 (mulRows 22 (mulRows 22 X Y) X) Y

@[expose] def glChartCoord (r k : Nat) : Int :=
  let c := glRootCoord[r]!
  let x := if k % 3 == 0 then c.1 else if k % 3 == 1 then c.2.1 else c.2.2
  if k < 3 then x else -x

@[expose] def glFrameConjRows (k : Nat) : Array Nat :=
  if k == 0 then idRows 22 else if k == 1 then glD1h else if k == 2 then mulRows 22 glD1h glD0h
  else if k == 3 then glW1 else if k == 4 then mulRows 22 glW1 glD1h
  else mulRows 22 (mulRows 22 glW1 glD1h) glD0h

@[expose] def glRootParOK : Bool :=
  (List.range 12).all fun r => [1, 2, 3].all fun t =>
    [1, 2, 3].all (fun s => mulRows 22 (glRootRows r s) (glRootRows r t) ==
      glRootRows r (s ^^^ t)) &&
    mulRows 22 (mulRows 22 (mulRows 22 glAl glAl) (glRootRows r t)) glAl ==
      glRootRows r (f4mul glRootChar[r]! t) &&
    glConj glGa (glRootRows r t) == glRootRows r (f4mul t t)

@[expose] def glRootCommOK : Bool :=
  (List.range 18).all fun a => (List.range 18).all fun b =>
    a == b || glOpp a b || (glParams a).all fun s => (glParams b).all fun t =>
      glCommRows (glRootRows a s) (glRootRows b t) == glProdRows (glCommLookup a b s t)

@[expose] def glChartOK : Bool :=
  (List.range 12).all (fun r => (List.range 6).all fun k =>
    decide (glChartCoord r k < 0) || [1, 2, 3].all fun t =>
      commRows (glRootRows r t) (glLongRows k)) &&
  (List.range 6).all fun k =>
    mulRows 22 (glFrameConjRows k) (glLongRows k) == mulRows 22 glZ (glFrameConjRows k)

@[expose] def glUOK : Bool :=
  [1, 2, 3].all (fun t =>
    glCommRows glU (glRootRows 2 t) == glRootRows 0 (f4mul t t) &&
    glCommRows glU (glRootRows 3 t) ==
      mulRows 22 (mulRows 22 glZ (glRootRows 0 t)) (glRootRows 1 (f4mul t t)) &&
    glCommRows glU (glRootRows 5 t) == glRootRows 0 t) &&
  [0, 1, 4].all (fun r => [1, 2, 3].all fun t => commRows glU (glRootRows r t)) &&
  [12, 13, 14].all (fun r => commRows glU (glRootRows r 1)) &&
  (List.range 18).all fun r => (glParams r).all fun t => glMaps (glRootRows r t) 80 80

@[expose] def glFrameOK : Bool :=
  let I := idRows 22
  (List.range 6).all (fun k => mulRows 22 (glLongRows k) (glLongRows k) == I) &&
    (List.range 3).all (fun i =>
      powRows 22 (mulRows 22 (glLongRows i) (glLongRows (i + 3))) 3 == I) &&
    (List.range 6).all (fun k => (List.range 6).all fun l =>
      k % 3 == l % 3 || commRows (glLongRows k) (glLongRows l)) &&
    mulRows 22 glD0h glD0h == I && mulRows 22 glD1h glD1h == I &&
    powRows 22 (mulRows 22 glD0h glD1h) 3 == I &&
    commRows glD0h glZ && commRows glD0h glX61 && commRows glD1h glX34 && commRows glD1h glX43

@[expose] def glRootOK : Bool := glRootParOK && glRootCommOK && glChartOK && glUOK && glFrameOK

@[expose] def glChainG0OK : Bool :=
  let S := glExtend (glOrig glG0Words) glChainG0W
  let L := rawLevels 2300 S glChainG0Base.toArray
  glChainOK glG0Words glChainG0Base glChainG0W 9196830720 &&
    glG0Words.all (fun w => glMaps (glR w) 80 80) && glPermOK glGa (glPermArr glGa) &&
    !siftA 2300 L glChainG0Base.toArray 0 (glPsiArr glGa) &&
    (List.range 18).all fun r => (glParams r).all fun t =>
      glPermOK (glRootRows r t) (glPermArr (glRootRows r t)) &&
        siftA 2300 L glChainG0Base.toArray 0 (glPsiArr (glRootRows r t))

end CFSG.Sporadic.Co2Smith.Native
