module

public import Std.Data.HashMap
public import Std.Data.HashSet

public section

namespace CFSG.LargeExtraspecial.Fin4.Native

set_option compiler.extract_closed false

@[expose] def col (c k : Nat) : Nat := c / 16 ^ k % 16

@[expose] def mk4 (a b c d : Nat) : Nat := a + 16 * b + 256 * c + 4096 * d

@[expose] def app (c v : Nat) : Nat :=
  (if v.testBit 0 then col c 0 else 0) ^^^ (if v.testBit 1 then col c 1 else 0) ^^^
    (if v.testBit 2 then col c 2 else 0) ^^^ (if v.testBit 3 then col c 3 else 0)

@[expose] def mulC (c d : Nat) : Nat :=
  mk4 (app c (col d 0)) (app c (col d 1)) (app c (col d 2)) (app c (col d 3))

@[expose] def idC (_ : Unit := ()) : Nat := mk4 1 2 4 8

@[expose] def Jn (x y : Nat) : Bool :=
  ((x.testBit 0 && y.testBit 2) ^^ (x.testBit 2 && y.testBit 0)) ^^
    ((x.testBit 1 && y.testBit 3) ^^ (x.testBit 3 && y.testBit 1))

@[expose] def isSpC (c : Nat) : Bool :=
  (List.range 4).all fun k => (List.range 4).all fun l =>
    Jn (col c k) (col c l) == Jn (2 ^ k) (2 ^ l)

@[expose] def inUC (v c : Nat) : Bool :=
  isSpC c && app c v == v &&
    (List.range 16).all (fun x => Jn v x || app c x ^^^ x == 0 || app c x ^^^ x == v) &&
    (List.range 16).all (fun y => !Jn v (app c y ^^^ y))

@[expose] def uList (v : Nat) : List Nat := (List.range 65536).filter (inUC v)

@[expose] def tauC (v : Nat) : Nat :=
  mk4 (1 ^^^ (if Jn 1 v then v else 0)) (2 ^^^ (if Jn 2 v then v else 0))
    (4 ^^^ (if Jn 4 v then v else 0)) (8 ^^^ (if Jn 8 v then v else 0))

@[expose] def quad (p q : Nat) : List Nat := [idC, p, q, mulC p q]

@[expose] def setEq (L M : List Nat) : Bool := L.all (M.contains ·) && M.all (L.contains ·)

@[expose] def cand (v : Nat) : List (List Nat) :=
  let U := uList v
  let qs := U.flatMap fun p => U.filterMap fun q =>
    if p != idC && q != idC && p < q && !(quad p q).contains (tauC v) then
      some ((quad p q).mergeSort (· ≤ ·))
    else none
  qs.eraseDups

@[expose] def quadOK (C : List (List Nat)) (t p q : Nat) : Bool :=
  p == idC || q == idC || p == q || (quad p q).contains t ||
    (mulC p q != idC && mulC p q != p && mulC p q != q && C.any (setEq · (quad p q)))

@[expose] def candOKAt (v : Nat) : Bool :=
  let U := uList v
  let C := cand v
  let t := tauC v
  U.all fun p => U.all fun q => quadOK C t p q

@[expose] def candOK (_ : Unit) : Bool := (List.range 16).all fun v => v == 0 || candOKAt v

end CFSG.LargeExtraspecial.Fin4.Native
