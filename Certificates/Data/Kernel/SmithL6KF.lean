module

public import Certificates.Data.Kernel.SmithL6K
public import Certificates.Data.Kernel.SmithL6Coll

public section

namespace CFSG.SmithL6.K

open CFSG.SmithL6 CFSG.SmithL6.CollK

@[expose] def kindC (c0 c : Nat) : Nat :=
  let a := form (c0 % 64) (c / 64)
  let b := form (c % 64) (c0 / 64)
  if a == b then (if a then 1 else 0) else 2

@[expose] def killK (F T : List Nat) : Bool :=
  (List.range 20).all fun m => apK F (T.getD m 0 ^^^ 2 ^ m) == 0

@[expose] def wordK (L : List (List Nat)) : List Nat → Nat → Nat
  | [], x => x
  | r :: w, x => apK (L.getD r []) (wordK L w x)

@[expose] def fRecK (C : List Nat) (L : List (List Nat)) (W : List Nat) (x0 : Nat)
    (e : Nat × Nat × Nat × List Nat) : Bool :=
  decide (e.1 < 1395) && W.getD e.1 0 == e.2.1 && decide (e.2.2.1 < 2 ^ 20) &&
    (apK (L.getD 0 []) e.2.2.1 ^^^ e.2.2.1) == e.2.1 &&
    e.2.2.2.all (fun r => decide (r < 1953) && kindC (C.getD 0 0) (C.getD r 0) == 0) &&
    wordK L e.2.2.2 x0 == e.2.1 && wordK L e.2.2.2.reverse e.2.1 == x0

@[expose] def fWordK (C : List Nat) (L : List (List Nat)) (W S : List Nat)
    (E : List (Nat × Nat × Nat × List Nat)) : Bool :=
  killK S (L.getD 0 []) &&
    W.all (fun x => apK S x != 0 || E.any fun e => e.2.1 == x) &&
    E.all (fRecK C L W (E.getD 0 (0, 0, 0, [])).2.1)

@[expose] def fPlaneK (C : List Nat) (L : List (List Nat)) (E : List (Nat × Nat × Nat × List Nat))
    (P : List (Nat × List Nat)) : Bool :=
  C.length == 1953 && L.length == 1953 && P.length == 1953 &&
    (C.zip (L.zip P)).all fun q => kindC (C.getD 0 0) q.1 != 2 ||
      (let x := (E.getD q.2.2.1 (0, 0, 0, [])).2.1
       decide (q.2.2.1 < E.length) && apK q.2.1 x == x && killK q.2.2.2 q.2.1 &&
         apK q.2.2.2 x != 0)

end CFSG.SmithL6.K
