module

public import Certificates.Data.Kernel.SporSch.LySyl

public section

namespace CFSG.KS.SporSch.LyGLQ

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch.LySyl

@[expose] noncomputable def gK : Nat := nat_lit 328449

@[expose] noncomputable def sgK (SG x : Nat) : Nat := fld(SG, Nat.mul (nat_lit 2) x, nat_lit 3)

@[expose] noncomputable def sigQ (MT : Nat → Nat) (SG x : Nat) : Bool :=
  Nat.beq (sgK SG x) (Nat.add (nIf(Nat.beq (tpowK MT x (nat_lit 2)) (nat_lit 0), nat_lit 2, nat_lit 0))
    (nIf(Nat.beq (tpowK MT x (nat_lit 4)) (nat_lit 0), nat_lit 1, nat_lit 0)))

@[expose] noncomputable def evK (MT : Nat → Nat) (y : Nat) (w : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun k _ acc => strictN acc (fun a => tmK MT (b8 y k) a)) w

@[expose] noncomputable def tstK (MT : Nat → Nat) (SG y : Nat) (w : List Nat) : Bool :=
  Nat.beq (sgK SG (evK MT y w)) (sgK SG (evK MT gK w))

@[expose] noncomputable def lvK (SG k : Nat) : List Nat :=
  (List.range 256).filter fun x => bAnd(Bool.not (Nat.beq x (nat_lit 0)),
    Nat.beq (sgK SG x) (sgK SG (b8 gK k)))

@[expose] noncomputable def grp0 (MT : Nat → Nat) (SG y : Nat) : Bool := tstK MT SG y [0]

@[expose] noncomputable def grp1 (MT : Nat → Nat) (SG y : Nat) : Bool :=
  bAnd(tstK MT SG y [1], bAnd(tstK MT SG y [0, 1], tstK MT SG y [1, 0]))

@[expose] noncomputable def grp2a (MT : Nat → Nat) (SG y : Nat) : Bool :=
  bAnd(tstK MT SG y [0, 2], tstK MT SG y [2, 0])

@[expose] noncomputable def grp2b (MT : Nat → Nat) (SG y : Nat) : Bool :=
  bAnd(tstK MT SG y [2], bAnd(tstK MT SG y [1, 2],
  bAnd(tstK MT SG y [2, 1], tstK MT SG y [0, 1, 2])))

@[expose] noncomputable def stage2 (MT : Nat → Nat) (SG a : Nat) : List Nat :=
  (fun L => (((lvK SG 1).map fun b => Nat.add a (Nat.mul (nat_lit 256) b)).filter
      (grp1 MT SG)).flatMap fun y =>
    (L.map fun c => Nat.add y (Nat.mul (nat_lit 65536) c)).filter (grp2b MT SG))
  ((lvK SG 2).filter fun c => grp2a MT SG (Nat.add a (Nat.mul (nat_lit 65536) c)))

@[expose] noncomputable def candsK (MT : Nat → Nat) (SG : Nat) : List Nat :=
  ((lvK SG 0).filter (grp0 MT SG)).flatMap (stage2 MT SG)

@[expose] noncomputable def getW (W : List (List Nat)) (t : Nat) : List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun x _ ih i => Nat.rec (motive := fun _ => List Nat) x (fun i' _ => ih i') i) W t

@[expose] noncomputable def eqL : List Nat → List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool)
    (fun m => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) m)
    (fun a _ ih m => List.rec (motive := fun _ => Bool) false
      (fun b m' _ => bAnd(Nat.beq a b, ih m')) m)

@[expose] noncomputable def getQ (Q : List Nat) (t : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun x _ ih i => Nat.rec (motive := fun _ => Nat) x (fun i' _ => ih i') i) Q t

@[expose] noncomputable def wStep (MT : Nat → Nat) (W : List (List Nat)) (x k : Nat) (Q : List Nat)
    (M : Nat) (cont : List Nat → Nat → Bool) : Bool :=
  strictB (tmK MT (b8 gK k) x) (fun z => bIf(hasBit M z, cont Q M,
    bAnd(eqL (getW W z) (k :: getW W x),
      cont (Q ++ [z]) (Nat.lor M (Nat.shiftLeft (nat_lit 1) z)))))

@[expose] noncomputable def wRun (MT : Nat → Nat) (W : List (List Nat)) : Nat → Nat → List Nat →
    Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → List Nat → Nat → Bool)
    (fun _ _ M => allN (nat_lit 256) (fun z => bIf(hasBit M z, true, eqL (getW W z) [])))
    (fun _ ih h Q M => bIf(Nat.blt h (lenL Q),
      strictB (getQ Q h) (fun x => wStep MT W x (nat_lit 0) Q M (fun Q M =>
        wStep MT W x (nat_lit 1) Q M (fun Q M => wStep MT W x (nat_lit 2) Q M (ih (Nat.succ h))))),
      ih (Nat.succ h) Q M))

@[expose] noncomputable def let3 (w : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun k _ ih => bAnd(Nat.blt k (nat_lit 3), ih)) w

@[expose] noncomputable def wordsK (MT : Nat → Nat) (W : List (List Nat)) : Bool :=
  bAnd(Nat.beq (lenL (W.map fun _ => nat_lit 0)) (nat_lit 256), bAnd(eqL (getW W (nat_lit 0)) [],
  bAnd(wRun MT W (nat_lit 256) (nat_lit 0) [nat_lit 0] (nat_lit 1),
    allN (nat_lit 256) (fun x => bAnd(Nat.beq (evK MT gK (getW W x)) x, let3 (getW W x))))))

@[expose] noncomputable def fK (MT : Nat → Nat) (W : List (List Nat)) (y : Nat) : Nat :=
  (List.rec (motive := fun _ => Nat → Nat → Nat) (fun _ acc => acc)
    (fun w _ ih x acc => strictN (Nat.lor acc (Nat.shiftLeft (evK MT y w) (Nat.mul (nat_lit 8) x)))
      (ih (Nat.succ x))) W) (nat_lit 0) (nat_lit 0)

@[expose] noncomputable def genT (MT : Nat → Nat) (W : List (List Nat)) (y t : Nat) : Bool :=
  strictB (Nat.shiftRight t (nat_lit 8)) (fun k => strictB (Nat.land t (nat_lit 255)) (fun x =>
    Nat.beq (evK MT y (getW W (tmK MT (b8 gK k) x))) (tmK MT (b8 y k) (evK MT y (getW W x)))))

@[expose] noncomputable def failK (MT : Nat → Nat) (W : List (List Nat)) (y n : Nat) : Bool :=
  Nat.rec (motive := fun _ => Nat → Bool) (fun _ => false)
    (fun _ ih t => bIf(genT MT W y t, ih (Nat.succ t), true)) n (nat_lit 0)

@[expose] noncomputable def critF (MT : Nat → Nat) (y F : Nat) : Bool :=
  bAnd(allN (nat_lit 255) (fun x => Bool.not (Nat.beq (b8 F (Nat.succ x)) (nat_lit 0))),
    allN (nat_lit 3) (fun k => strictB (b8 gK k) (fun g => strictB (b8 y k) (fun yk =>
      allN (nat_lit 256) (fun x => Nat.beq (b8 F (tmK MT g x)) (tmK MT yk (b8 F x)))))))

@[expose] noncomputable def critK (MT : Nat → Nat) (W : List (List Nat)) (y : Nat) : Bool :=
  strictB (fK MT W y) (critF MT y)

@[expose] noncomputable def autsK (MT : Nat → Nat) (W : List (List Nat)) :
    List Nat → List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool)
    (fun A => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) A)
    (fun y _ ih A => List.rec (motive := fun _ => Bool) (bAnd(failK MT W y (nat_lit 768), ih A))
      (fun a A' _ => bIf(Nat.beq y a, bAnd(critK MT W y, ih A'),
        bAnd(failK MT W y (nat_lit 768), ih A))) A)

@[expose] noncomputable def assocQ (MT : Nat → Nat) (k : Nat) : Bool :=
  strictB (b8 gK k) (fun g => allN (nat_lit 256) (fun a => strictB (tmK MT g a) (fun ga =>
    allN (nat_lit 256) (fun b => Nat.beq (tmK MT ga b) (tmK MT g (tmK MT a b))))))

@[expose] noncomputable def invoF (F : Nat) : Bool :=
  allN (nat_lit 256) (fun x => Nat.beq (b8 F (b8 F x)) x)

@[expose] noncomputable def pairsK (MT : Nat → Nat) : List Nat :=
  ((List.range 256).filter fun a => bAnd(Bool.not (Nat.beq a (nat_lit 0)),
    Nat.beq (tmK MT a a) (nat_lit 0))).flatMap fun a =>
  (((List.range 256).filter fun b => bAnd(Bool.not (Nat.beq b (nat_lit 0)),
    Nat.beq (tmK MT b b) (nat_lit 0))).filter fun b =>
      bAnd(Nat.blt a b, Nat.beq (tmK MT a b) (tmK MT b a))).map fun b =>
        Nat.add a (Nat.mul (nat_lit 256) b)

@[expose] noncomputable def fixF (P : List Nat) (F : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun p _ ih =>
    bIf(bAnd(Nat.beq (b8 F (b8 p 0)) (b8 p 0), Nat.beq (b8 F (b8 p 1)) (b8 p 1)), true, ih)) P

@[expose] noncomputable def invoCnt (MT : Nat → Nat) (W : List (List Nat)) (P : List Nat) :
    List Nat → Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun y _ ih => strictN (fK MT W y) (fun F =>
    nIf(invoF F, nIf(fixF P F, Nat.succ ih, nat_lit 1048576), ih)))

end CFSG.KS.SporSch.LyGLQ

end
