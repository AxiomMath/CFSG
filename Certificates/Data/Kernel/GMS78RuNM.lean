module

public import Certificates.Data.Kernel.GMS78RuN

public section

namespace CFSG.KC.GMS

open CFSG.KLie.CT CFSG.KC.Loop

@[expose] noncomputable def gllAt (GLL i : Nat) : Nat := fget GLL i (nat_lit 9)

@[expose] noncomputable def gllOK (GLL : Nat) : Bool :=
  andB (allN (nat_lit 168) fun i => glK (gllAt GLL i))
  (andB (allN (nat_lit 167) fun i => Nat.blt (nIdxK (gllAt GLL i)) (nIdxK (gllAt GLL (Nat.succ i))))
    (Nat.beq (sumN (nat_lit 512) fun R => nIf(glK R, nat_lit 1, nat_lit 0)) (nat_lit 168)))

@[expose] noncomputable def bindTW (ntw : List (List (Fin 8))) (GLL TW : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun i => Nat.beq i (nat_lit 168))
    (fun row _ ih i => andB (bindFin8 row (fget TW (gllAt GLL i) (nat_lit 24)) (nat_lit 8)) (ih (Nat.succ i)))
    ntw (nat_lit 0)

@[expose] noncomputable def tauF (T G m : Nat) : Nat :=
  (fun c => Nat.xor (xs8K c fun j => fget T j (nat_lit 3))
      (xs8K c fun j => xs8K c fun i => fget G (Nat.add (Nat.mul (nat_lit 8) i) j) (nat_lit 3)))
    (maskAppK NCOLS m)

@[expose] noncomputable def rOK (INV TW ADC TAU R : Nat) : Bool :=
  strictB (adK R (fget INV R (nat_lit 9))) fun A => andB (Nat.beq (fget ADC R (nat_lit 64)) A)
    (strictB (gamTab R A) fun G => strictB (fget TW R (nat_lit 24)) fun T =>
      Nat.beq (fget TAU R (nat_lit 768)) (orN (nat_lit 256) fun m =>
        Nat.shiftLeft (tauF T G m) (Nat.mul (nat_lit 3) m)))

@[expose] noncomputable def adA (ADC R m : Nat) : Nat := maskAppK (fget ADC R (nat_lit 64)) m

@[expose] noncomputable def tauA (TAU R m : Nat) : Nat := fget (fget TAU R (nat_lit 768)) m (nat_lit 3)

@[expose] noncomputable def kQuad (ADC TAU R : Nat) : Bool :=
  strictB (fget ADC R (nat_lit 64)) fun CR => strictB (fget TAU R (nat_lit 768)) fun TR =>
  allN (nat_lit 8) fun i => allN (nat_lit 8) fun j => (fun m b => Nat.beq (fget TR (Nat.xor m b) (nat_lit 3))
      (Nat.xor (Nat.xor (fget TR m (nat_lit 3)) (fget TR b (nat_lit 3)))
        (Nat.xor (nBetaK (maskAppK CR m) (maskAppK CR b)) (linAppK R (nBetaK m b)))))
    (fget NBAS i (nat_lit 8)) (fget NBAS j (nat_lit 8))

@[expose] noncomputable def kComp (GLL ADC TAU R : Nat) : Bool :=
  strictB (fget ADC R (nat_lit 64)) fun CR => strictB (fget TAU R (nat_lit 768)) fun TR =>
  allN (nat_lit 168) fun s => strictB (gllAt GLL s) fun S => strictB (linCompK R S) fun RS =>
    strictB (fget ADC S (nat_lit 64)) fun CS => strictB (fget ADC RS (nat_lit 64)) fun CRS =>
    strictB (fget TAU S (nat_lit 768)) fun TS => strictB (fget TAU RS (nat_lit 768)) fun TRS =>
    allN (nat_lit 8) fun k =>
      andB (Nat.beq (fget CRS k (nat_lit 8)) (maskAppK CR (fget CS k (nat_lit 8))))
        ((fun b => Nat.beq (fget TRS b (nat_lit 3))
            (Nat.xor (fget TR (maskAppK CS b) (nat_lit 3)) (linAppK R (fget TS b (nat_lit 3)))))
          (fget NBAS k (nat_lit 8)))

@[expose] noncomputable def nmR (GLL INV TW ADC TAU R : Nat) : Bool :=
  andB (rOK INV TW ADC TAU R) (andB (kQuad ADC TAU R) (kComp GLL ADC TAU R))

@[expose] noncomputable def kId (GLL INV ADC TAU : Nat) : Bool :=
  strictB (fget ADC LINID (nat_lit 64)) fun C1 => strictB (fget TAU LINID (nat_lit 768)) fun T1 =>
  andB (allN (nat_lit 256) fun m => andB (Nat.beq (maskAppK C1 m) m) (andB (Nat.beq (fget T1 m (nat_lit 3)) (nat_lit 0))
    (Nat.beq (maskAppK NBAS (maskAppK NCOLS m)) m)))
  (andB (allN (nat_lit 512) fun R => orB (notB (glK R)) ((fun I => andB (glK I)
      (andB (Nat.beq (linCompK I R) LINID) (Nat.beq (linCompK R I) LINID))) (fget INV R (nat_lit 9))))
    (allN (nat_lit 168) fun i => allN (nat_lit 168) fun j => glK (linCompK (gllAt GLL i) (gllAt GLL j))))

@[expose] noncomputable def kFaith (FW : Nat) : Bool :=
  andB (allN (nat_lit 255) fun m => (fun n => andB (Nat.blt n (nat_lit 256))
      (notB (Nat.beq (nBetaK (Nat.succ m) n) (nBetaK n (Nat.succ m))))) (fget FW m (nat_lit 8)))
    (allN (nat_lit 8) fun t => allN (nat_lit 8) fun t' => orB (Nat.beq t (nat_lit 0)) (orB (Nat.beq t' (nat_lit 0))
      (anyN (nat_lit 512) fun S => andB (glK S) (Nat.beq (linAppK S t) t'))))

@[expose] noncomputable def trM (P : Nat) : Nat := fget P (nat_lit 0) (nat_lit 8)
@[expose] noncomputable def trT (P : Nat) : Nat := fget (Nat.shiftRight P (nat_lit 8)) (nat_lit 0) (nat_lit 3)
@[expose] noncomputable def trR (P : Nat) : Nat := Nat.shiftRight P (nat_lit 11)

@[expose] noncomputable def ONET : Nat := Nat.shiftLeft LINID (nat_lit 11)

@[expose] noncomputable def mulT (ADC TAU P Q : Nat) : Nat :=
  (fun m t R m' t' R' => (fun am => Nat.lor (Nat.xor m am) (Nat.lor
      (Nat.shiftLeft (Nat.xor (Nat.xor t (Nat.xor (linAppK R t') (tauA TAU R m'))) (nBetaK m am)) (nat_lit 8))
      (Nat.shiftLeft (linCompK R R') (nat_lit 11)))) (adA ADC R m'))
    (trM P) (trT P) (trR P) (trM Q) (trT Q) (trR Q)

@[expose] noncomputable def sgnK (NIMG NIMGI c : Nat) : Nat :=
  nIf(Nat.beq (Nat.mod c (nat_lit 2)) (nat_lit 0), fget NIMG (Nat.div c (nat_lit 2)) (nat_lit 20),
    fget NIMGI (Nat.div c (nat_lit 2)) (nat_lit 20))

@[expose] noncomputable def evalC (ADC TAU NIMG NIMGI : Nat) (w : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun x => x)
    (fun c _ ih x => strictN (nIf(Nat.blt c (nat_lit 14), mulT ADC TAU x (sgnK NIMG NIMGI c), x)) ih) w ONET

@[expose] noncomputable def evalS (ADC TAU NIMG NIMGI : Nat) (w : List (Fin 7 × Bool)) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun x => x)
    (fun l _ ih x => strictN (Prod.rec (motive := fun _ => Nat) (fun i s =>
      mulT ADC TAU x (nIf(s, fget NIMG i.val (nat_lit 20), fget NIMGI i.val (nat_lit 20)))) l) ih) w ONET

@[expose] noncomputable def kImg (ADC TAU NIMG NIMGI : Nat) : Bool :=
  allN (nat_lit 7) fun i => (fun P Q => andB (glK (trR P)) (andB (glK (trR Q))
      (Nat.beq (mulT ADC TAU P Q) ONET)))
    (fget NIMG i (nat_lit 20)) (fget NIMGI i (nat_lit 20))

@[expose] noncomputable def kRel (rels : List (List Nat)) (ADC TAU NIMG NIMGI : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun w _ ih => andB (Nat.beq (evalC ADC TAU NIMG NIMGI w) ONET) ih) rels

@[expose] noncomputable def kClo (rW kW : List (List Nat)) (GLL ADC TAU NIMG NIMGI NRT : Nat) : Bool :=
  andB (List.rec (motive := fun _ => Nat → Bool) (fun i => Nat.beq i (nat_lit 11))
      (fun w _ ih i => andB (Nat.beq (evalC ADC TAU NIMG NIMGI w) (fget NRT i (nat_lit 20))) (ih (Nat.succ i)))
      rW (nat_lit 0))
    (List.rec (motive := fun _ => Nat → Bool) (fun i => Nat.beq i (nat_lit 168))
      (fun w _ ih i => andB (Nat.beq (evalC ADC TAU NIMG NIMGI w) (Nat.shiftLeft (gllAt GLL i) (nat_lit 11)))
        (ih (Nat.succ i)))
      kW (nat_lit 0))

@[expose] noncomputable def kA0 (a0 : List (List (Fin 7 × Bool))) (ADC TAU NIMG NIMGI : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun w _ ih => andB ((fun P => andB (Nat.beq (trM P) (nat_lit 0)) (Nat.beq (trR P) LINID))
      (evalS ADC TAU NIMG NIMGI w)) ih) a0

@[expose] noncomputable def packT (p : Nat × Fin 8 × (Fin 8 × Fin 8 × Fin 8)) : Nat :=
  Prod.rec (motive := fun _ => Nat) (fun m tr => Prod.rec (motive := fun _ => Nat) (fun t r =>
    Nat.lor m (Nat.lor (Nat.shiftLeft t.val (nat_lit 8)) (Nat.shiftLeft (packV r) (nat_lit 11)))) tr) p

@[expose] noncomputable def smallM (L : List (Nat × Fin 8 × (Fin 8 × Fin 8 × Fin 8))) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun p _ ih => andB (Prod.rec (motive := fun _ => Bool)
    (fun m _ => Nat.blt m (nat_lit 256)) p) ih) L

@[expose] noncomputable def bindImg (img imgInv rT : List (Nat × Fin 8 × (Fin 8 × Fin 8 × Fin 8)))
    (NIMG NIMGI NRT : Nat) : Bool :=
  andB (bindList packT img NIMG (nat_lit 20) (nat_lit 7))
  (andB (bindList packT imgInv NIMGI (nat_lit 20) (nat_lit 7))
  (andB (bindList packT rT NRT (nat_lit 20) (nat_lit 11))
    (andB (smallM img) (smallM imgInv))))

@[expose] noncomputable def zeroOK (ADC TAU : Nat) : Bool :=
  allN (nat_lit 512) fun R => orB (glK R)
    (andB (Nat.beq (fget ADC R (nat_lit 64)) (nat_lit 0)) (Nat.beq (fget TAU R (nat_lit 768)) (nat_lit 0)))

end CFSG.KC.GMS

end
