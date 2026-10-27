module

public import Certificates.Data.Kernel.Fin76bAut

public section

namespace CFSG.KS.EAut

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.Row CFSG.KS.PEnum

@[expose] noncomputable def eAnyN (n : Nat) (f : Nat → Bool) : Bool :=
  bIf(allN n (fun i => bIf(f i, false, true)), false, true)

@[expose] noncomputable def eBEq (a b : Bool) : Bool := bIf(a, b, bIf(b, false, true))

@[expose] noncomputable def eZ (x : Nat) : Bool :=
  bIf(Nat.beq x (nat_lit 0), true, Nat.beq x (nat_lit 21))

@[expose] noncomputable def eCm (ET : Nat → Nat) (x y : Nat) : Bool :=
  Nat.beq (eMul ET x y) (eMul ET y x)

@[expose] noncomputable def eCnt (n : Nat) (f : Nat → Bool) : Nat :=
  foldUp n (fun i acc => nIf(f i, Nat.succ acc, acc)) (nat_lit 0)

@[expose] noncomputable def eCtrK (ET : Nat → Nat) : Bool :=
  allN (nat_lit 32) (fun x => eBEq (allN (nat_lit 32) (fun y => eCm ET x y)) (eZ x))

@[expose] noncomputable def eGenStep (ET : Nat → Nat) (S k R : Nat) : Nat :=
  foldUp (nat_lit 32) (fun a acc => nIf(hasBit R a,
    foldUp k (fun j acc2 =>
      Nat.lor acc2 (Nat.shiftLeft (nat_lit 1) (eMul ET a (eG S j)))) acc, acc)) R

@[expose] noncomputable def eGenReach (ET : Nat → Nat) (S k f : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 1)
    (fun _ ih => strictN ih (fun R => eGenStep ET S k R)) f

@[expose] noncomputable def eGenK (ET : Nat → Nat) (S k f : Nat) : Bool :=
  Nat.beq (eGenReach ET S k f) (nat_lit 4294967295)

@[expose] noncomputable def eTupOk (ET : Nat → Nat) (GN d X x : Nat) : Bool :=
  strictB (eG GN d) (fun g => bAnd(eBEq (eZ x) (eZ g),
    bAnd(Nat.beq (eMul ET x x) (eMul ET g g),
      allN d (fun i => eBEq (eCm ET (eG X i) x) (eCm ET (eG GN i) g)))))

@[expose] noncomputable def eTupRec (ET : Nat → Nat) (GN : Nat) : Nat → Nat → Nat → Nat :=
  fun r => Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ _ => nat_lit 1)
    (fun _ ih d X => foldUp (nat_lit 32) (fun x acc => nIf(eTupOk ET GN d X x,
      Nat.add acc (ih (Nat.succ d) (Nat.lor X (Nat.shiftLeft x (Nat.mul (nat_lit 6) d)))), acc))
      (nat_lit 0)) r

@[expose] noncomputable def eTupCnt (ET : Nat → Nat) (GN k : Nat) : Nat :=
  eTupRec ET GN k (nat_lit 0) (nat_lit 0)

@[expose] noncomputable def eTupK (ET : Nat → Nat) (GN k f c : Nat) : Bool :=
  bAnd(eCtrK ET, bAnd(allN k (fun d => strictB (eG GN d) (fun g =>
      bAnd(Nat.blt g (nat_lit 32), eZ (eMul ET g g)))),
    bAnd(eGenK ET GN k f, Nat.beq (eTupCnt ET GN k) c)))

@[expose] noncomputable def eInPr (ET : Nat → Nat) (r k : Nat) : Bool :=
  bIf(Nat.beq k r, true, Nat.beq k (eMul ET r (nat_lit 21)))

@[expose] noncomputable def ePrRep (ET : Nat → Nat) (r : Nat) : Bool :=
  bAnd(eKind ET (nat_lit 0) r, Nat.blt r (eMul ET r (nat_lit 21)))

@[expose] noncomputable def ePrK (ET : Nat → Nat) (PR : Nat) : Bool :=
  bAnd(Nat.beq (eMul ET (nat_lit 21) (nat_lit 21)) (nat_lit 0),
  bAnd(Nat.beq (eCnt (nat_lit 32) (fun r => ePrRep ET r)) (nat_lit 5),
    allN (nat_lit 5) (fun j => strictB (eG PR j) (fun r =>
      bAnd(Nat.blt r (nat_lit 32), bAnd(ePrRep ET r,
        bIf(Nat.blt (Nat.succ j) (nat_lit 5), Nat.blt r (eG PR (Nat.succ j)), true)))))))

@[expose] noncomputable def ePidx (ET : Nat → Nat) (PR k : Nat) : Nat :=
  foldUp (nat_lit 5) (fun j acc => nIf(eInPr ET (eG PR j) k, j, acc)) (nat_lit 0)

@[expose] noncomputable def eSigAt (ET : Nat → Nat) (PR p j : Nat) : Nat :=
  ePidx ET PR (eG p (eG PR j))

@[expose] noncomputable def eTriv (ET : Nat → Nat) (PR p : Nat) : Bool :=
  allN (nat_lit 5) (fun j => strictB (eG PR j) (fun r => eInPr ET r (eG p r)))

@[expose] noncomputable def eEven (ET : Nat → Nat) (PR p : Nat) : Bool :=
  Nat.beq (Nat.land (foldUp (nat_lit 5) (fun i acc => strictN (eSigAt ET PR p i) (fun si =>
    foldUp i (fun j acc2 => nIf(Nat.blt si (eSigAt ET PR p j), Nat.succ acc2, acc2)) acc))
    (nat_lit 0)) (nat_lit 1)) (nat_lit 0)

@[expose] noncomputable def eKerK (ET : Nat → Nat) (PR cnt : Nat) (T : Nat → Nat) (ni : Nat)
    (INN : Nat → Nat) : Bool :=
  allN cnt (fun i => strictB (T i) (fun p => bAnd(Nat.beq (eG p (nat_lit 21)) (nat_lit 21),
    eBEq (eTriv ET PR p) (eAnyN ni (fun u => Nat.beq (INN u) i)))))

@[expose] noncomputable def eBInv (ET : Nat → Nat) (PR p : Nat) : Bool :=
  bAnd(eInvK p, bAnd(eEven ET PR p, bIf(eTriv ET PR p, false, true)))

@[expose] noncomputable def eFixK (ET : Nat → Nat) (p : Nat) : Bool :=
  bAnd(Nat.beq (eCnt (nat_lit 32) (fun x => Nat.beq (eG p x) x)) (nat_lit 4),
    allN (nat_lit 32) (fun x => bIf(Nat.beq (eG p x) x, Nat.beq (eMul ET x x) (nat_lit 0), true)))

@[expose] noncomputable def eCocK (ET : Nat → Nat) (p : Nat) : Bool :=
  allN (nat_lit 32) (fun e => bIf(Nat.beq (eMul ET e (eG p e)) (nat_lit 0),
    eAnyN (nat_lit 32) (fun c => Nat.beq (eMul ET e (eG p c)) c), true))

@[expose] noncomputable def eCommG (GN k p q : Nat) : Bool :=
  allN k (fun j => strictB (eG GN j) (fun g => Nat.beq (eG p (eG q g)) (eG q (eG p g))))

@[expose] noncomputable def eInvG (GN k p : Nat) : Bool :=
  bAnd(allN k (fun j => strictB (eG GN j) (fun g => Nat.beq (eG p (eG p g)) g)),
    bIf(Nat.beq p eId, false, true))

@[expose] noncomputable def eKlX (A B AB b : Nat) : Nat :=
  nIf(Nat.beq b (nat_lit 0), eId, nIf(Nat.beq b (nat_lit 1), A, nIf(Nat.beq b (nat_lit 2), B, AB)))

@[expose] noncomputable def eKlAt (T INN : Nat → Nat) (A B AB s y : Nat) : Nat :=
  eG (T (INN (Nat.shiftRight s (nat_lit 2)))) (eG (eKlX A B AB (Nat.land s (nat_lit 3))) y)

@[expose] noncomputable def eKlComm (GN k : Nat) (T INN : Nat → Nat) (A B AB s s' : Nat) : Bool :=
  allN k (fun j => strictB (eG GN j) (fun g =>
    Nat.beq (eKlAt T INN A B AB s (eKlAt T INN A B AB s' g))
      (eKlAt T INN A B AB s' (eKlAt T INN A B AB s g))))

@[expose] noncomputable def eKlSq (GN k : Nat) (T INN : Nat → Nat) (A B AB s : Nat) : Bool :=
  allN k (fun j => strictB (eG GN j) (fun g =>
    Nat.beq (eKlAt T INN A B AB s (eKlAt T INN A B AB s g)) g))

@[expose] noncomputable def eKlGen (A B e : Nat) : Nat :=
  Nat.lor e (Nat.lor (Nat.shiftLeft (eG A e) (nat_lit 6))
    (Nat.lor (Nat.shiftLeft (eG B e) (nat_lit 12)) (Nat.shiftLeft (eG A (eG B e)) (nat_lit 18))))

@[expose] noncomputable def eKleinK (ET : Nat → Nat) (GN k f : Nat) (T INN : Nat → Nat) (A B : Nat) :
    Bool :=
  strictB (eC A B) (fun AB =>
    bAnd(allN (nat_lit 32) (fun x => bIf(Nat.beq (eG A x) x, Nat.beq (eG B x) x, true)),
    bAnd(eAnyN (nat_lit 32) (fun e => eGenK ET (eKlGen A B e) (nat_lit 4) f),
      allN (nat_lit 64) (fun s => bIf(eKlSq GN k T INN A B AB s,
        Nat.ble (nat_lit 16) (eCnt (nat_lit 64) (fun s' => eKlComm GN k T INN A B AB s s')),
        true)))))

@[expose] noncomputable def e613FixK (ET : Nat → Nat) (PR : Nat) (T : Nat → Nat) (nr : Nat)
    (REP : Nat → Nat) : Bool :=
  allN nr (fun r => strictB (T (REP r)) (fun A =>
    bIf(eBInv ET PR A, bAnd(eFixK ET A, eCocK ET A), true)))

@[expose] noncomputable def eKlPart (ET : Nat → Nat) (GN k PR A B : Nat) : Bool :=
  bAnd(eBInv ET PR B, bAnd(bIf(Nat.beq A B, false, true),
    bAnd(eCommG GN k A B, bIf(eTriv ET PR (eC A B), false, true))))

@[expose] noncomputable def e613KlK (ET : Nat → Nat) (GN k f PR : Nat) (T : Nat → Nat) (nr : Nat)
    (REP : Nat → Nat) (nv : Nat) (IV : Nat → Nat) (INN : Nat → Nat) : Bool :=
  allN nr (fun r => strictB (T (REP r)) (fun A => bIf(eBInv ET PR A,
    allN nv (fun q => strictB (T (IV q)) (fun B =>
      bIf(eKlPart ET GN k PR A B, eKleinK ET GN k f T INN A B, true))), true)))

@[expose] noncomputable def e614K (GN k cnt : Nat) (T : Nat → Nat) (nr : Nat) (REP : Nat → Nat) :
    Bool :=
  allN nr (fun r => strictB (T (REP r)) (fun A =>
    Nat.beq (Nat.mod (eCnt cnt (fun i => eCommG GN k (T i) A)) (nat_lit 32)) (nat_lit 0)))

@[expose] noncomputable def e615K (GN k cntS : Nat) (ST : Nat → Nat) : Bool :=
  Nat.blt (eCnt cntS (fun i => strictB (ST i) (fun x => bAnd(eInvG GN k x,
    Nat.ble (nat_lit 31) (eCnt cntS (fun j => strictB (ST j) (fun y =>
      bAnd(eInvG GN k y, eCommG GN k x y)))))))) (nat_lit 31)

end CFSG.KS.EAut

end
