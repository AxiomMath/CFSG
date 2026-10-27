module

public import CFSG.Certificates.Kernel.Th.S.BigS
public import CFSG.Certificates.Kernel.Common.Loop

public section

namespace CFSG.KC.ThCensus

open CFSG.KC.Th.BigS CFSG.KC.Loop

@[expose] noncomputable def permStep (TT g d p : Nat) : Nat :=
  nIf(Nat.beq d (nat_lit 0), p,
    bitsN TT (Nat.mul (nat_lit 8) (Nat.add (Nat.mul (nat_lit 243)
      (Nat.sub (Nat.add (Nat.mul (nat_lit 2) g) d) (nat_lit 1))) p)) (nat_lit 8))

@[expose] noncomputable def permWalkFrom (TT : Nat) : Nat → Nat → Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat) (fun _ p _ => p)
    (fun _ ih g p n => strictN (permStep TT g (Nat.mod n (nat_lit 3)) p)
      (fun q => ih (Nat.succ g) q (Nat.div n (nat_lit 3))))

@[expose] noncomputable def permWalk (TT p n : Nat) : Nat := permWalkFrom TT (nat_lit 10) (nat_lit 0) p n

@[expose] noncomputable def permNfNum (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun d _ acc => Nat.add d (Nat.mul (nat_lit 3) acc)) l

@[expose] noncomputable def permTtRowOK (TT g : Nat) (l : List Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun t _ ih j => bAnd(Nat.beq (permStep TT g (nat_lit 1) j) t,
      bAnd(Nat.beq (permStep TT g (nat_lit 2) j) (permStep TT g (nat_lit 1) t), ih (Nat.succ j)))) l

@[expose] noncomputable def permTtOK (TT g : Nat) (l : List Nat) : Bool := permTtRowOK TT g l (nat_lit 0)

@[expose] noncomputable def permCubeFix (TT o n : Nat) : Bool :=
  Nat.beq (permWalk TT (permWalk TT (permWalk TT o n) n) n) o

@[expose] noncomputable def permKeyAt (TT o c n r : Nat) : Bool :=
  Nat.beq (permWalk TT (permWalk TT o c) n) (permWalk TT (permWalk TT o r) c)

@[expose] noncomputable def permRecOK (TT : Nat) (reps : List (List Nat)) (nr o0 o1 o2 n rc : Nat) : Bool :=
  (fun m1 c => bAnd(Nat.blt (nat_lit 0) m1, bAnd(Nat.ble m1 nr,
    (fun r => bAnd(permKeyAt TT o0 c n r, bAnd(permKeyAt TT o1 c n r, permKeyAt TT o2 c n r)))
      (permNfNum (reps.getD (Nat.sub m1 (nat_lit 1)) [])))))
    (Nat.mod rc (nat_lit 64)) (Nat.div rc (nat_lit 64))

@[expose] noncomputable def permElemOK (TT R : Nat) (reps : List (List Nat)) (nr o0 o1 o2 b i : Nat) :
    Bool :=
  (fun n => bIf(Nat.beq n (nat_lit 0), true,
    bAnd(notB (bAnd(Nat.beq (permWalk TT o0 n) o0, bAnd(Nat.beq (permWalk TT o1 n) o1,
        Nat.beq (permWalk TT o2 n) o2))),
      bIf(bAnd(permCubeFix TT o0 n, bAnd(permCubeFix TT o1 n, permCubeFix TT o2 n)),
        permRecOK TT reps nr o0 o1 o2 n (bitsN R (Nat.mul (nat_lit 24) i) (nat_lit 24)), true))))
    (Nat.add (Nat.mul (nat_lit 729) b) i)

@[expose] noncomputable def permBlockOK (TT R : Nat) (reps : List (List Nat)) (nr o0 o1 o2 b : Nat) : Bool :=
  allBelow (nat_lit 729) (nat_lit 12) (fun i => permElemOK TT R reps nr o0 o1 o2 b i)

@[expose] noncomputable def permNfListOK (L : List (List Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun l _ ih => bAnd(Nat.beq (List.rec (motive := fun _ => Nat) (nat_lit 0)
        (fun _ _ acc => Nat.succ acc) l) (nat_lit 10),
      bAnd(List.rec (motive := fun _ => Bool) true (fun d _ ih2 => bAnd(Nat.blt d (nat_lit 3), ih2)) l,
        ih))) L

end CFSG.KC.ThCensus

end
