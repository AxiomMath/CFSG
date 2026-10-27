module

public import Certificates.Data.Kernel.He7222.Cover

public section

namespace CFSG.KC.HeChain

open CFSG.KC.Enum CFSG.KS CFSG.KC.OrbRow

@[expose] noncomputable def getLL (L : List (List (List Nat))) : Nat → List (List Nat) :=
  List.rec (motive := fun _ => Nat → List (List Nat)) (fun _ => List.nil)
    (fun x _ ih j => Nat.rec (motive := fun _ => List (List Nat)) x (fun i _ => ih i) j) L

@[expose] noncomputable def invK (n w m idn T TI : Nat) : Bool :=
  bAnd(Nat.beq (Nat.shiftRight TI (Nat.mul n w)) (nat_lit 0),
    bAnd(Nat.blt (pg w m TI (nat_lit 0)) n, Nat.beq (pcomp n w m T TI) idn))

@[expose] noncomputable def invLK (n w m idn : Nat) (T TI : List Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun j => Nat.beq j (lenS TI))
    (fun t _ ih j => bAnd(invK n w m idn t (getS TI j), strictB (Nat.succ j) ih)) T (nat_lit 0)

@[expose] noncomputable def tupOK : List (List Nat) → List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool)
    (fun ix => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) ix)
    (fun T _ ih ix => List.rec (motive := fun _ => Bool) false
      (fun j ixr _ => bAnd(Nat.blt j (lenS T), ih ixr)) ix)

@[expose] noncomputable def stkK : List (List Nat) → List Nat → List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) (fun _ => List.nil)
    (fun T _ ih ix => List.rec (motive := fun _ => List Nat) List.nil
      (fun j ixr _ => List.cons (getS T j) (ih ixr)) ix)

@[expose] noncomputable def stkIK : List (List Nat) → List Nat → List Nat → List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat → List Nat) (fun _ acc => acc)
    (fun TI _ ih ix acc => List.rec (motive := fun _ => List Nat) acc
      (fun j ixr _ => ih ixr (List.cons (getS TI j) acc)) ix)

@[expose] noncomputable def cjEv (w m : Nat) (cs rs cis : List Nat) (p : Nat) : Nat :=
  evK w m cs (evK w m rs (evK w m cis p))

@[expose] noncomputable def keyF (w : Nat) (f : Nat → Nat) (nf : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun k ih => Nat.lor ih (Nat.shiftLeft (f k) (Nat.mul w k))) nf

@[expose] noncomputable def clsK (w m : Nat) (Ts TIs : List (List Nat)) (rs : List Nat)
    (KC : List (List Nat)) (keys : List Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun pos => Nat.beq pos (lenS keys))
    (fun ix _ ih pos => bAnd(tupOK Ts ix,
      bAnd(Nat.beq (keyF w (cjEv w m (stkK Ts ix) rs (stkIK TIs ix List.nil)) (nat_lit 5))
        (getS keys pos), strictB (Nat.succ pos) ih)))
    KC (nat_lit 0)

@[expose] noncomputable def cmK (w m : Nat) (cs rs cis : List Nat) (h hI tau : Nat) : Bool :=
  allN (nat_lit 5) (fun k =>
    Nat.beq (cjEv w m cs rs cis (pg w m hI (pg w m tau (pg w m h k))))
      (pg w m hI (pg w m tau (pg w m h (cjEv w m cs rs cis k)))))

@[expose] noncomputable def svK (w m : Nat) (Ts TIs : List (List Nat)) (rs : List Nat)
    (h hI tau : Nat) (KC : List (List Nat)) (Sv : List Nat) : Bool :=
  List.rec (motive := fun _ => Nat → List Nat → Bool)
    (fun _ sv => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) sv)
    (fun ix _ ih pos sv => strictB (Nat.succ pos) (fun pos' =>
      List.rec (motive := fun _ => Bool)
        (bIf(cmK w m (stkK Ts ix) rs (stkIK TIs ix List.nil) h hI tau, false, ih pos' sv))
        (fun q rest _ => bIf(Nat.beq q pos, ih pos' rest,
          bIf(cmK w m (stkK Ts ix) rs (stkIK TIs ix List.nil) h hI tau, false, ih pos' sv)))
        sv))
    KC (nat_lit 0) Sv

end CFSG.KC.HeChain

end
