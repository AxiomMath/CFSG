module

public import Certificates.Data.Kernel.SmithL6K
public import Certificates.Data.Kernel.SmithL6Coll

public section

namespace CFSG.SmithL6.K

open CFSG.SmithL6 CFSG.SmithL6.CollK

@[expose] def projL (V U : List Nat) (w : Nat) : Nat :=
  (List.range V.length).foldl (fun acc t => if fB w (U.getD t 0) then acc ^^^ V.getD t 0 else acc) 0

@[expose] def dualL (n : Nat) (V U : List Nat) : Bool :=
  (List.range n).all fun s => (List.range n).all fun t => fB (V.getD s 0) (U.getD t 0) == (s == t)

@[expose] def zipAllK (f : Nat → Nat → Bool) : List Nat → List Nat → Bool
  | a :: A, b :: B => f a b && zipAllK f A B
  | [], [] => true
  | _, _ => false

@[expose] def qaVecsK (W : List Nat) (C : List (List Nat)) (G : List (Nat × Nat)) : List Nat :=
  G.map fun pk => apK (C.getD pk.1 []) (W.getD pk.2 0) ^^^ W.getD pk.2 0

@[expose] def qaChkK (W Ms : List Nat) (C : List (List Nat)) (P : List Nat) (G : List (Nat × Nat))
    (U : List Nat) : Bool :=
  G.length == 10 && U.length == 10 &&
    G.all (fun pk => P.contains pk.1 && decide (pk.2 < 1395) && !fB (W.getD 0 0) (W.getD pk.2 0)) &&
    dualL 10 (qaVecsK W C G) U &&
    zipAllK (fun w m => atLeast4 (Ms.getD 0 0 &&& m) == (projL (qaVecsK W C G) U w == w)) W Ms

@[expose] def cvVecsK (C : List (List Nat)) (G : List (Nat × Nat)) : List Nat :=
  G.map fun pm => apK (C.getD pm.1 []) (2 ^ pm.2) ^^^ 2 ^ pm.2

@[expose] def cvChkK (W : List Nat) (C : List (List Nat)) (P : List Nat) (G : List (Nat × Nat))
    (U : List Nat) : Bool :=
  G.length == 19 && U.length == 19 &&
    P.all (fun p => apK (C.getD p []) (W.getD 0 0) == W.getD 0 0) &&
    G.all (fun pm => P.contains pm.1 && decide (pm.2 < 20)) &&
    (List.range 20).all fun m =>
      (2 ^ m ^^^ projL U (cvVecsK C G) (2 ^ m)) == 0 ||
        (2 ^ m ^^^ projL U (cvVecsK C G) (2 ^ m)) == W.getD 0 0

end CFSG.SmithL6.K
