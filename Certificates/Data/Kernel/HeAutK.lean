module

public import Certificates.Data.Kernel.HexaK

public section

namespace CFSG.KC.HeAutK

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KC.HexaK
open CFSG.KLie.CT (anyN andB orB notB)

@[expose] noncomputable def eqB (a b : Bool) : Bool := Bool.rec (notB b) b a

@[expose] noncomputable def inZ (n w z t : Nat) : Bool :=
  strictB t fun t => orB (Nat.beq t (pidn n w)) (Nat.beq t z)

@[expose] noncomputable def commZ (n w z a b : Nat) : Bool :=
  strictB a fun a => strictB b fun b => strictB (mul n w a b) fun ab => strictB (mul n w b a) fun ba =>
    orB (Nat.beq ab ba) (Nat.beq ab (mul n w ba z))

@[expose] noncomputable def bitK (F i : Nat) : Bool :=
  Nat.beq (Nat.land (Nat.shiftRight F i) (nat_lit 1)) (nat_lit 1)

@[expose] noncomputable def pw (n w a k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (pidn n w) (fun _ acc => strictN acc fun acc => mul n w a acc) k

@[expose] noncomputable def flagsK (n w N : Nat) (T : Nat → Nat) (z FZ F1 : Nat) : Bool :=
  allN N fun i => strictB (T i) fun x => strictB (mul n w x x) fun q =>
    andB (eqB (bitK FZ i) (inZ n w z q)) (eqB (bitK F1 i) (Nat.beq q (pidn n w)))

@[expose] noncomputable def cntR (f : Nat → Bool) (lo len : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun k acc => strictN acc fun a => Nat.add a (Bool.rec (nat_lit 0) (nat_lit 1) (f (Nat.add lo k))))
    len

@[expose] noncomputable def allR (f : Nat → Bool) (lo len : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun k acc => andB acc (f (Nat.add lo k))) len

@[expose] noncomputable def setYK (n w N : Nat) (T : Nat → Nat) (FZ z x : Nat) : List Nat :=
  Nat.rec (motive := fun _ => List Nat → List Nat) (fun acc => acc)
    (fun r ih acc => Bool.rec (motive := fun _ => List Nat) (ih acc) (ih (r :: acc))
      (andB (bitK FZ r) (commZ n w z x (T r)))) N []

@[expose] noncomputable def goodQK (n w N : Nat) (T : Nat → Nat) (FZ z x : Nat) : Bool :=
  strictB (setYK n w N T FZ z x).length fun c => orB (Nat.blt c (nat_lit 128))
    (andB (Nat.beq c (nat_lit 128)) ((setYK n w N T FZ z x).any fun a =>
      (setYK n w N T FZ z x).any fun b => notB (commZ n w z (T a) (T b))))

@[expose] noncomputable def uqAt (n w NX : Nat) (TX : Nat → Nat) (NQ : Nat) (TQ : Nat → Nat)
    (FZ z i : Nat) : Bool :=
  andB (bitK FZ i) (strictB (TX i) fun x =>
    andB (notB (inL NQ TQ x)) (notB (goodQK n w NX TX FZ z x)))

@[expose] noncomputable def ueAt (n w NX : Nat) (TX : Nat → Nat) (NE : Nat) (TE : Nat → Nat)
    (NF : Nat) (TF : Nat → Nat) (F1 i : Nat) : Bool :=
  orB (notB (bitK F1 i)) (strictB (TX i) fun x => orB (Nat.beq x (pidn n w))
    (orB (inL NE TE x) (orB (inL NF TF x)
      (Nat.blt (cntR (fun j => andB (bitK F1 j) (comm n w x (TX j))) (nat_lit 0) NX) (nat_lit 64)))))

@[expose] noncomputable def elemAbK (n w N : Nat) (T : Nat → Nat) (g : Nat) (G : Nat → Nat) : Bool :=
  andB (allN N fun i => strictB (T i) fun x => Nat.beq (mul n w x x) (pidn n w))
    (allN g fun a => allN g fun b => comm n w (G a) (G b))

@[expose] noncomputable def restK (n w gX : Nat) (GX : Nat → Nat) (NX : Nat) (TX : Nat → Nat)
    (gQ : Nat) (GQ : Nat → Nat) (NQ : Nat) (TQ : Nat → Nat)
    (gE : Nat) (GE : Nat → Nat) (NE : Nat) (TE : Nat → Nat)
    (gF : Nat) (GF : Nat → Nat) (NF : Nat) (TF : Nat → Nat)
    (gU : Nat) (GU : Nat → Nat) (NU : Nat) (TU : Nat → Nat) (z r s : Nat) : Bool :=
  andB (allN gQ fun k => inL NX TX (GQ k))
  (andB (allN gE fun k => inL NX TX (GE k))
  (andB (allN gF fun k => inL NX TX (GF k))
  (andB (allN gU fun k => inL NQ TQ (GU k))
  (andB (inL NQ TQ z) (andB (inL NX TX r) (andB (inL NX TX s)
  (andB (allN gX fun k => allN gQ fun q => inL NQ TQ (conj n w (GX k) (GQ q)))
  (andB (allN gQ fun k => allN gE fun q => inL NE TE (conj n w (GQ k) (GE q)))
  (andB (allN gQ fun k => allN gF fun q => inL NF TF (conj n w (GQ k) (GF q)))
  (andB (Nat.beq (mul n w z z) (pidn n w)) (andB (notB (Nat.beq z (pidn n w)))
  (andB (allN gX fun k => comm n w z (GX k))
  (andB (allN NX fun i => strictB (TX i) fun x =>
    orB (notB (allN gX fun k => comm n w x (GX k))) (inZ n w z x))
  (andB (allN NQ fun i => strictB (TQ i) fun x => inZ n w z (mul n w x x))
  (andB (allN NQ fun i => strictB (TQ i) fun x =>
    orB (notB (allN gQ fun k => comm n w x (GQ k))) (inZ n w z x))
  (andB (anyN gQ fun a => anyN gQ fun b => notB (comm n w (GQ a) (GQ b)))
  (andB (elemAbK n w NE TE gE GE) (andB (elemAbK n w NF TF gF GF) (andB (elemAbK n w NU TU gU GU)
  (andB (anyN gE fun a => notB (inL NF TF (GE a)))
  (andB (inL NQ TQ (pw n w r 8)) (andB (inL NQ TQ (mul n w s s))
  (andB (inL NQ TQ (strictN (mul n w s r) fun t => mul n w t t))
  (andB (allN 7 fun i => notB (inL NQ TQ (pw n w r (Nat.succ i))))
    (allN 8 fun i => notB (inL NQ TQ (mul n w s (pw n w r i))))))))))))))))))))))))))))

end CFSG.KC.HeAutK

end
