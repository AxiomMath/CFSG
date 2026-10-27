module

public import Certificates.Data.Kernel.GMS78RuNM

public section

namespace CFSG.KC.GMS

open CFSG.KLie.CT CFSG.KC.Loop

@[expose] noncomputable def inX0K (P : Nat) : Bool :=
  andB (Nat.beq (Nat.land (trM P) (nat_lit 207)) (nat_lit 0)) (Nat.beq (trR P) LINID)

@[expose] noncomputable def conjK (ADC TAU g gi x : Nat) : Nat := mulT ADC TAU (mulT ADC TAU g x) gi

@[expose] noncomputable def sameK (ADC TAU Z0P y y' : Nat) : Bool :=
  orB (Nat.beq y y') (Nat.beq y (mulT ADC TAU y' Z0P))

@[expose] noncomputable def kZ0 (z0w : List (Fin 7 × Bool)) (ADC TAU NIMG NIMGI Z0P : Nat) : Bool :=
  Nat.beq (evalS ADC TAU NIMG NIMGI z0w) Z0P

@[expose] noncomputable def kLetter (ADC TAU NIMG NIMGI XP Z0P : Nat) : Bool :=
  allN (nat_lit 5) fun i => (fun g gi => andB (Nat.beq (mulT ADC TAU g Z0P) (mulT ADC TAU Z0P g))
      (allN (nat_lit 32) fun k => (fun x => andB (inX0K (conjK ADC TAU g gi x))
        (inX0K (conjK ADC TAU gi g x))) (fget XP k (nat_lit 20))))
    (fget NIMG i (nat_lit 20)) (fget NIMGI i (nat_lit 20))

@[expose] noncomputable def invRevK (w : List (Fin 7 × Bool)) :
    List (Fin 7 × Bool) → List (Fin 7 × Bool) :=
  List.rec (motive := fun _ => List (Fin 7 × Bool) → List (Fin 7 × Bool)) (fun acc => acc)
    (fun l _ ih acc => ih (List.cons (Prod.rec (motive := fun _ => Fin 7 × Bool)
      (fun i s => (i, Bool.rec (motive := fun _ => Bool) true false s)) l) acc)) w

@[expose] noncomputable def kJ (ws : List (List (Fin 7 × Bool))) (ADC TAU NIMG NIMGI XP Z0P : Nat) :
    Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun w _ ih => andB ((fun g gi => allN (nat_lit 32) fun k => (fun x =>
        sameK ADC TAU Z0P (conjK ADC TAU g gi x) x) (fget XP k (nat_lit 20)))
      (evalS ADC TAU NIMG NIMGI w) (evalS ADC TAU NIMG NIMGI (invRevK w []))) ih) ws

@[expose] noncomputable def imgsK (ADC TAU NIMG NIMGI XP : Nat) (w : List (Fin 7 × Bool)) : Nat :=
  (fun g gi => orN (nat_lit 32) fun k =>
      Nat.shiftLeft (conjK ADC TAU g gi (fget XP k (nat_lit 20))) (Nat.mul (nat_lit 20) k))
    (evalS ADC TAU NIMG NIMGI w) (evalS ADC TAU NIMG NIMGI (invRevK w []))

@[expose] noncomputable def imgsListK (ADC TAU NIMG NIMGI XP : Nat) (ws : List (List (Fin 7 × Bool))) :
    List Nat :=
  List.rec (motive := fun _ => List Nat) [] (fun w _ ih => List.cons (imgsK ADC TAU NIMG NIMGI XP w) ih) ws

@[expose] noncomputable def diffK (ADC TAU Z0P U V : Nat) : Bool :=
  notB (allN (nat_lit 32) fun k => sameK ADC TAU Z0P (fget U k (nat_lit 20)) (fget V k (nat_lit 20)))

@[expose] noncomputable def diffAllK (ADC TAU Z0P U : Nat) (Vs : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun V _ ih => andB (diffK ADC TAU Z0P U V) ih) Vs

@[expose] noncomputable def pairDiffK (ADC TAU Z0P : Nat) (Vs : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun U rest ih => andB (diffAllK ADC TAU Z0P U rest) ih) Vs

@[expose] noncomputable def kRep (ws : List (List (Fin 7 × Bool))) (ADC TAU NIMG NIMGI XP Z0P : Nat) :
    Bool :=
  andB (Nat.beq (List.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ _ ih => Nat.succ ih) ws)
      (nat_lit 24))
    (pairDiffK ADC TAU Z0P (imgsListK ADC TAU NIMG NIMGI XP ws))

@[expose] noncomputable def conjCodeK (INV C R : Nat) : Nat :=
  linCompK (linCompK C R) (fget INV C (nat_lit 9))

@[expose] noncomputable def kInvol (GLL INV W : Nat) : Bool :=
  allN (nat_lit 168) fun g => (fun R ws => orB
      (notB (andB (Nat.beq (linCompK R R) LINID) (notB (Nat.beq R LINID))))
      (allN (nat_lit 8) fun k => andB (Nat.blt (fget ws k (nat_lit 8)) (nat_lit 168))
        (andB (Nat.blt (fget ws (Nat.succ k) (nat_lit 8)) (nat_lit 168))
          (Nat.blt (conjCodeK INV (gllAt GLL (fget ws k (nat_lit 8))) R)
            (conjCodeK INV (gllAt GLL (fget ws (Nat.succ k) (nat_lit 8))) R)))))
    (gllAt GLL g) (fget W g (nat_lit 72))

end CFSG.KC.GMS

end
