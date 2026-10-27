module

public import Certificates.Data.Kernel.ThLocal.Defs

public section

namespace CFSG.KC.ThLocal

open CFSG.KC.Th CFSG.KC.Th.BigS CFSG.KC.Loop CFSG.KC.ThCensus

@[expose] noncomputable def moveAt (TT o r x y v : Nat) : Bool :=
  notB (Nat.beq (iterW TT y (Nat.div v (nat_lit 27))
    (iterW TT x (Nat.mod (Nat.div v (nat_lit 9)) (nat_lit 3))
      (iterW TT (nat_lit 19683) (Nat.mod (Nat.div v (nat_lit 3)) (nat_lit 3))
        (iterW TT r (Nat.mod v (nat_lit 3)) o)))) o)

@[expose] noncomputable def movesOK (TT o0 o1 o2 r x y : Nat) (m : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun i ih => bAnd(orB (moveAt TT o0 r x y (Nat.succ i))
      (orB (moveAt TT o1 r x y (Nat.succ i)) (moveAt TT o2 r x y (Nat.succ i))), ih)) m

@[expose] noncomputable def e81OK (TT o0 o1 o2 r x y : Nat) : Bool :=
  bAnd(key3 TT o0 o1 o2 x r r, bAnd(key3 TT o0 o1 o2 y r r, bAnd(key3 TT o0 o1 o2 x y y,
    bAnd(cube3 TT o0 o1 o2 x, bAnd(cube3 TT o0 o1 o2 y, movesOK TT o0 o1 o2 r x y (nat_lit 80))))))

@[expose] noncomputable def e81RepOK (TT o0 o1 o2 : Nat) (reps : List (List Nat)) (m : Nat)
    (E : List Nat) : Bool :=
  (fun r => orB (isZ r) (e81OK TT o0 o1 o2 r (E.getD 0 0) (E.getD 1 0)))
    (permNfNum (reps.getD m []))

end CFSG.KC.ThLocal

end
