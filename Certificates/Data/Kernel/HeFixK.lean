module

public import Certificates.Data.Kernel.HeAutK

public section

namespace CFSG.KC.HeFixK

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KC.HexaK CFSG.KC.HeAutK
open CFSG.KLie.CT (fget anyN andB orB notB)

@[expose] noncomputable def closK (n w nb N SA SB SM q t j : Nat) : Bool :=
  strictB q fun q => strictB t fun t =>
  andB (canonK (nat_lit 32) (nat_lit 6) (mask (nat_lit 6)) (nat_lit 192) q)
    (allN N fun i => strictB (fget SM (Nat.add (Nat.mul (nat_lit 6) i) j) (nat_lit 12)) fun m =>
      andB (Nat.blt m N) (strictB (fget SA i (nat_lit 192)) fun a =>
        andB (canonK (nat_lit 32) (nat_lit 6) (mask (nat_lit 6)) (nat_lit 192) a)
          (andB (Nat.beq (fget SA m (nat_lit 192)) (pcomp (nat_lit 32) (nat_lit 6) (mask (nat_lit 6)) q a))
            (strictB (fget SB i (Nat.mul nb w)) fun b => strictB (fget SB m (Nat.mul nb w)) fun b' =>
              allN nb fun k => strictB (pg w (mask w) b k) fun x =>
                andB (Nat.blt x n) (Nat.beq (pg w (mask w) t x) (pg w (mask w) b' k))))))

@[expose] noncomputable def fixK (n w p : Nat) : Nat :=
  strictN p fun p => cntR (fun i => Nat.beq (pg w (mask w) p i) i) (nat_lit 0) n

@[expose] noncomputable def cenK (N : Nat) (T : Nat → Nat) (g : Nat) (G : Nat → Nat) : Nat :=
  cntR (fun i => strictB (T i) fun x => allN g fun k => comm (nat_lit 32) (nat_lit 6) x (G k))
    (nat_lit 0) N

@[expose] noncomputable def eK (g : Nat) (G : Nat → Nat) : Bool :=
  andB (allN g fun a => allN g fun b => comm (nat_lit 32) (nat_lit 6) (G a) (G b))
    (allN g fun a => strictB (G a) fun x =>
      Nat.beq (mul (nat_lit 32) (nat_lit 6) x x) (pidn (nat_lit 32) (nat_lit 6)))

@[expose] noncomputable def normK (gT : Nat) (GT : Nat → Nat) (NE : Nat) (TE : Nat → Nat)
    (gE : Nat) (GE : Nat → Nat) : Bool :=
  allN gT fun j => allN gE fun i =>
    andB (inL NE TE (conj (nat_lit 32) (nat_lit 6) (GT j) (GE i)))
      (inL NE TE (conjInv (nat_lit 32) (nat_lit 6) (GT j) (GE i)))

@[expose] noncomputable def itK (N : Nat) (T : Nat → Nat) (IT : Nat) : Bool :=
  allN N fun j => strictB (T j) fun x =>
    eqB (bitK IT j) (Nat.beq (mul (nat_lit 32) (nat_lit 6) x x) (pidn (nat_lit 32) (nat_lit 6)))

@[expose] noncomputable def e8K (x y z : Nat) : Bool :=
  strictB (pidn (nat_lit 32) (nat_lit 6)) fun e =>
  andB (Nat.beq (mul (nat_lit 32) (nat_lit 6) x x) e)
  (andB (Nat.beq (mul (nat_lit 32) (nat_lit 6) y y) e)
  (andB (Nat.beq (mul (nat_lit 32) (nat_lit 6) z z) e)
  (andB (comm (nat_lit 32) (nat_lit 6) x y) (andB (comm (nat_lit 32) (nat_lit 6) x z)
  (andB (comm (nat_lit 32) (nat_lit 6) y z)
  (andB (notB (Nat.beq x e)) (andB (notB (Nat.beq y e)) (andB (notB (Nat.beq y x))
  (andB (notB (Nat.beq z e)) (andB (notB (Nat.beq z x)) (andB (notB (Nat.beq z y))
    (notB (Nat.beq z (mul (nat_lit 32) (nat_lit 6) x y))))))))))))))

@[expose] noncomputable def tripK (N : Nat) (T : Nat → Nat) (a b c : Nat) : Bool :=
  strictB (fget c (nat_lit 0) (nat_lit 10)) fun i => strictB (fget c (nat_lit 1) (nat_lit 10)) fun j =>
  strictB (fget c (nat_lit 2) (nat_lit 10)) fun k =>
  andB (Nat.blt i N) (andB (Nat.blt j N) (andB (Nat.blt k N)
    (strictB (T i) fun x => strictB (T j) fun y => strictB (T k) fun z =>
      andB (e8K x y z)
        (andB (andB (comm (nat_lit 32) (nat_lit 6) x a) (comm (nat_lit 32) (nat_lit 6) x b))
          (andB (andB (comm (nat_lit 32) (nat_lit 6) y a) (comm (nat_lit 32) (nat_lit 6) y b))
            (andB (comm (nat_lit 32) (nat_lit 6) z a) (comm (nat_lit 32) (nat_lit 6) z b)))))))

@[expose] noncomputable def pairK (N : Nat) (T : Nat → Nat) (IT WT a c j : Nat) : Nat :=
  nIf(Nat.beq c (nat_lit 0), nat_lit 0,
    nIf(bitK IT j, strictN (T j) fun b =>
      nIf(comm (nat_lit 32) (nat_lit 6) b a,
        nIf(tripK N T a b (fget WT (Nat.sub c (nat_lit 1)) (nat_lit 30)), Nat.succ c, nat_lit 0), c), c))

@[expose] noncomputable def innerK (N : Nat) (T : Nat → Nat) (IT WT a c : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun c => c)
    (fun r ih c => strictN (pairK N T IT WT a c (Nat.sub (Nat.sub N r) (nat_lit 1))) ih) N c

@[expose] noncomputable def outerAt (TA : Nat → Nat) (N : Nat) (T : Nat → Nat)
    (IT WT i c : Nat) : Nat :=
  strictN (TA i) fun a => nIf(Nat.beq c (nat_lit 0), nat_lit 0,
    nIf(Nat.beq (mul (nat_lit 32) (nat_lit 6) a a) (pidn (nat_lit 32) (nat_lit 6)),
      nIf(inL N T a, c, innerK N T IT WT a c), c))

@[expose] noncomputable def outerK (NA : Nat) (TA : Nat → Nat) (N : Nat) (T : Nat → Nat)
    (IT WT : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun c => c)
    (fun r ih c => strictN (outerAt TA N T IT WT (Nat.sub (Nat.sub NA r) (nat_lit 1)) c) ih)
    NA (nat_lit 1)

end CFSG.KC.HeFixK

end
