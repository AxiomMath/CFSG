module

public import Certificates.Data.Kernel.ThCensus.PermDefs
public import Certificates.Data.Kernel.ThCensus.Words

public section

namespace CFSG.KC.ThLocal

open CFSG.KC.Th CFSG.KC.Th.BigS CFSG.KC.Loop CFSG.KC.ThCensus

@[expose] noncomputable def key3 (TT o0 o1 o2 c n r : Nat) : Bool :=
  bAnd(permKeyAt TT o0 c n r, bAnd(permKeyAt TT o1 c n r, permKeyAt TT o2 c n r))

@[expose] noncomputable def cube3 (TT o0 o1 o2 n : Nat) : Bool :=
  bAnd(permCubeFix TT o0 n, bAnd(permCubeFix TT o1 n, permCubeFix TT o2 n))

@[expose] noncomputable def zcOK (TT o0 o1 o2 : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun k ih => bAnd(key3 TT o0 o1 o2 (Nat.pow (nat_lit 3) k) (nat_lit 19683) (nat_lit 19683), ih))
    (nat_lit 10)

@[expose] noncomputable def headN (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun a _ _ => a) l

@[expose] noncomputable def tailN (l : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) [] (fun _ t _ => t) l

@[expose] noncomputable def headL (L : List (List Nat)) : List Nat :=
  List.rec (motive := fun _ => List Nat) [] (fun e _ _ => e) L

@[expose] noncomputable def memH (x : Nat) (L : List (List Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun e _ ih => orB (Nat.beq (headN e) x) ih) L

@[expose] noncomputable def clsRowOK (TT o0 o1 o2 : Nat) (L : List (List Nat)) (s : Nat) :
    List Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun s' _ ih k => bAnd(memH s' L, bAnd(key3 TT o0 o1 o2 (Nat.pow (nat_lit 3) k) s s',
      ih (Nat.succ k))))

@[expose] noncomputable def clsRowsOK (TT o0 o1 o2 : Nat) (L : List (List Nat)) (M : List (List Nat)) :
    Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun e _ ih => bAnd(Nat.beq (lenN e) (nat_lit 11),
      bAnd(clsRowOK TT o0 o1 o2 L (headN e) (tailN e) (nat_lit 0), ih))) M

@[expose] noncomputable def clsOK (TT o0 o1 o2 : Nat) (L : List (List Nat)) : Bool :=
  clsRowsOK TT o0 o1 o2 L L

@[expose] noncomputable def isZ (n : Nat) : Bool :=
  orB (Nat.beq n (nat_lit 19683)) (Nat.beq n (nat_lit 39366))

@[expose] noncomputable def zRep (reps : List (List Nat)) (fus : List (List Nat)) (f : Nat) : Nat :=
  nIf(Nat.beq f (nat_lit 50), nat_lit 19683, nIf(Nat.beq f (nat_lit 51), nat_lit 39366,
    permNfNum (reps.getD ((fus.getD f []).getD 0 0) [])))

@[expose] noncomputable def zRepOK (tgts fus : List (List Nat)) (f : Nat) : Bool :=
  bAnd(Nat.blt f (nat_lit 52), orB (Nat.ble (nat_lit 50) f)
    (isZ (permNfNum (tgts.getD ((fus.getD f []).getD 1 0) []))))

@[expose] noncomputable def iterW (TT n : Nat) (a : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun p => p)
    (fun _ ih p => strictN (permWalk TT p n) ih) a

@[expose] noncomputable def e9KeyAt (TT o e1 e2 a b c r : Nat) : Bool :=
  Nat.beq (iterW TT e2 b (iterW TT e1 a (permWalk TT o c))) (permWalk TT (permWalk TT o r) c)

@[expose] noncomputable def e9RecOK (TT o0 o1 o2 : Nat) (reps tgts fus : List (List Nat))
    (e1 e2 a b c f : Nat) : Bool :=
  bAnd(zRepOK tgts fus f, (fun r => bAnd(e9KeyAt TT o0 e1 e2 a b c r,
    bAnd(e9KeyAt TT o1 e1 e2 a b c r, e9KeyAt TT o2 e1 e2 a b c r))) (zRep reps fus f))

@[expose] noncomputable def e9RecsOK (TT o0 o1 o2 : Nat) (reps tgts fus : List (List Nat))
    (E : List Nat) (e1 e2 : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun i ih => bAnd(e9RecOK TT o0 o1 o2 reps tgts fus e1 e2 (Nat.div (Nat.succ i) (nat_lit 3))
      (Nat.mod (Nat.succ i) (nat_lit 3)) (E.getD (Nat.add (nat_lit 2) (Nat.mul (nat_lit 2) i)) 0)
      (E.getD (Nat.add (nat_lit 3) (Nat.mul (nat_lit 2) i)) 0), ih)) (nat_lit 8)

@[expose] noncomputable def e9OK (TT o0 o1 o2 : Nat) (reps tgts fus : List (List Nat)) (t : Nat)
    (E : List Nat) : Bool :=
  (fun e1 e2 => bAnd(key3 TT o0 o1 o2 e1 t t, bAnd(key3 TT o0 o1 o2 e2 t t,
    bAnd(key3 TT o0 o1 o2 e1 e2 e2, bAnd(cube3 TT o0 o1 o2 e1, bAnd(cube3 TT o0 o1 o2 e2,
      e9RecsOK TT o0 o1 o2 reps tgts fus E e1 e2))))))
    (E.getD 0 0) (E.getD 1 0)

@[expose] noncomputable def tgtLocOK (TT o0 o1 o2 : Nat) (reps tgts fus : List (List Nat)) (j : Nat)
    (L : List (List Nat)) (E : List Nat) : Bool :=
  (fun t => bAnd(Nat.beq (headN (headL L)) t, bAnd(Nat.ble (lenN L) (nat_lit 27),
    bAnd(clsOK TT o0 o1 o2 L, e9OK TT o0 o1 o2 reps tgts fus t E))))
    (permNfNum (tgts.getD j []))

@[expose] noncomputable def invOK (RB : Nat → Nat) (c rm ONE r2 r3 rz n w : Nat) : Bool :=
  (fun W => bAnd(Nat.beq (mulB c rm W W) ONE, bAnd(notB (Nat.beq (mulB c rm W ONE) ONE),
    Nat.beq (mulB c rm W (RB rz)) (mulB c rm (RB rz) W))))
    (wordR RB c rm (nat_lit 1) (nat_lit 2) r2 r3 n w ONE)

end CFSG.KC.ThLocal

end
