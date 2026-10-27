module

public import Certificates.Data.Kernel.SporSch.Co1RankCand
public import Certificates.Data.Kernel.Co1BW

public section

namespace CFSG.KC.Co1RankTab

open CFSG.KC.Loop CFSG.KC.Co1B CFSG.KC.Co1RankCoord

structure Dat where
  d : Nat
  Kt : Nat
  NCt : Nat
  PHt : Nat
  nG : Nat
  REL : Nat
  CW : List Nat
  G : List Nat
  BS : List Nat
  WL : List Nat
  cM : Nat
  T2A : List (List Nat)
  nU : Nat
  UC : Nat
  P : List Nat

@[expose] noncomputable def toC (D : Dat) : Co1RankCoord.Dat := ⟨D.d, D.Kt, D.NCt, D.PHt, 0, []⟩

@[expose] noncomputable def getM (L : List Nat) (k : Nat) : Nat := CFSG.KC.Co1F2.getL oneK L k

@[expose] noncomputable def relK (D : Dat) (j g : Nat) : Nat :=
  fld(D.REL, Nat.mul (Nat.add 7 D.d) (Nat.add (Nat.mul D.nG j) g), mask (Nat.add 7 D.d))

@[expose] noncomputable def stepC (D : Dat) (x g : Nat) : Nat :=
  strictN (relK D (Nat.shiftRight x D.d) g) fun r =>
  Nat.lor (Nat.shiftLeft (Nat.land r 127) D.d) (Nat.xor (Nat.land x (mask D.d)) (Nat.shiftRight r 7))

@[expose] noncomputable def walkC (D : Dat) (w x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ x => x)
    (fun _ ih w x => strictN (Nat.land w 15) fun l =>
      nIf(Nat.beq l 0, x, strictN (stepC D x (Nat.sub l 1)) fun x' => ih (Nat.shiftRight w 4) x'))
    8 w x

@[expose] noncomputable def walkM (G : List Nat) (w acc : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ a => a)
    (fun _ ih w a => strictN (Nat.land w 15) fun l =>
      nIf(Nat.beq l 0, a, strictN (mulWK a (getM G (Nat.sub l 1))) fun a' => ih (Nat.shiftRight w 4) a'))
    8 w acc

@[expose] noncomputable def phRow (D : Dat) (i : Nat) : Nat :=
  fld(D.PHt, Nat.mul (Nat.mul D.d D.d) i, mask (Nat.mul D.d D.d))

@[expose] noncomputable def chkT (D : Dat) : Bool :=
  bAnd(Nat.beq (getL D.CW 0) 0,
  bAnd(allBelow 16384 256 fun p =>
      strictB (Nat.shiftRight p 7) fun i => strictB (Nat.land p 127) fun j =>
      Nat.beq (walkC D (getL D.CW j) (Nat.shiftLeft i D.d))
        (Nat.lor (Nat.shiftLeft (kt D.Kt i j) D.d) (nc D.d D.NCt i j)),
    allBelow 16384 256 fun p =>
      strictB (Nat.shiftRight p 7) fun i => strictB (Nat.land p 127) fun j =>
      bIf(Nat.blt i j, bIf(Nat.beq (phRow D i) (phRow D j), false, true), true)))

@[expose] noncomputable def qOf (D : Dat) (v : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) oneK (fun s acc =>
    nIf(Nat.beq (Nat.land (Nat.shiftRight v s) 1) 1, strictN acc fun a => mulWK a (getM D.BS s), acc)) D.d

@[expose] noncomputable def eltM (D : Dat) (x : Nat) : Nat :=
  mulWK (qOf D (Nat.land x (mask D.d))) (getM D.WL (Nat.shiftRight x D.d))

@[expose] noncomputable def indepOK (bs : List Nat) : Bool :=
  List.rec (motive := fun _ => List Nat → Bool) (fun _ => true)
    (fun b _ ih L =>
      (fun L' => bAnd(List.rec (motive := fun _ => Bool) true
        (fun x _ ih2 => bIf(Nat.beq x oneK, false, ih2)) L', ih (List.append L L')))
      (List.rec (motive := fun _ => List Nat) [] (fun a _ ih => List.cons (mulWK a b) ih) L))
    bs [oneK]

@[expose] noncomputable def chkM (D : Dat) : Bool :=
  bAnd(Nat.rec (motive := fun _ => Bool) true (fun s ih => bAnd(
      Nat.rec (motive := fun _ => Bool) true (fun t ih2 =>
        strictB (getM D.BS s) fun a => strictB (getM D.BS t) fun b =>
        bAnd(Nat.beq (mulWK a b) (mulWK b a), ih2)) D.d,
      bAnd(Nat.beq (mulWK (getM D.BS s) (getM D.BS s)) oneK, ih))) D.d,
  bAnd(indepOK D.BS,
  bAnd(Nat.rec (motive := fun _ => Bool) true (fun i ih =>
      bAnd(Nat.beq (getM D.WL i) (walkM D.G (getL D.CW i) oneK), ih)) 128,
  bAnd(Nat.rec (motive := fun _ => Bool) true (fun j ih => strictB (getM D.WL j) fun W =>
      bAnd(Nat.rec (motive := fun _ => Bool) true (fun g ih2 => strictB (relK D j g) fun r =>
        bAnd(Nat.beq (mulWK W (getM D.G g))
          (mulWK (qOf D (Nat.shiftRight r 7)) (getM D.WL (Nat.land r 127))), ih2)) D.nG,
      bAnd(Nat.rec (motive := fun _ => Bool) true (fun s ih2 =>
        bAnd(Nat.beq (mulWK W (getM D.BS s))
          (mulWK (qOf D (phi D.d D.PHt j (Nat.shiftLeft 1 s))) W), ih2)) D.d, ih))) 128,
  bAnd(Nat.beq (eltM D (fld(D.UC, 0, mask (Nat.add D.d 7)))) D.cM,
  Nat.rec (motive := fun _ => Bool) true (fun j ih =>
    strictB (getL (Co1RankCand.getLL D.T2A (Nat.shiftRight j 3)) (Nat.land j 7)) fun T =>
    bAnd(allBelow (Nat.shiftLeft 1 D.d) (Nat.shiftLeft 1 (Nat.sub D.d 6)) fun v =>
      bIf(Nat.beq (fld(T, v, 1)) 1,
        Nat.beq (rankRC 24 24 (Nat.xor (eltM D (Nat.lor (Nat.shiftLeft j D.d) v)) oneK)) 8, true),
      ih)) 128)))))

@[expose] noncomputable def chkP (D : Dat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun g ih =>
    strictB (stepC D 0 g) fun xg => strictB (getL D.P g) fun Pg =>
    bAnd(allBelow D.nU (Nat.succ (Nat.shiftRight D.nU 6)) fun u =>
      strictB (fld(Pg, Nat.mul 12 u, 4095)) fun u' =>
      bAnd(Nat.blt u' D.nU,
        Nat.beq (mulC (toC D) xg (fld(D.UC, Nat.mul (Nat.add D.d 7) u, mask (Nat.add D.d 7))))
          (stepC D (fld(D.UC, Nat.mul (Nat.add D.d 7) u', mask (Nat.add D.d 7))) g)), ih)) D.nG

end CFSG.KC.Co1RankTab

end
