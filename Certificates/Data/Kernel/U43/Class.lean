module

public import Certificates.Data.Kernel.U43.Fast

public section

namespace CFSG.KD.U43

open CFSG.KC.Loop CFSG.RankThree.PartTwo.Sec4.Item434RemU43

@[expose] noncomputable def letB (v : Nat) (k : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k (nat_lit 0)) (fun n _ => k (Nat.succ n)) v

@[expose] noncomputable def parF (X G : Nat → Nat) (K : Nat) (par : List (Nat × Nat)) :
    Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun ps _ ih i => bAnd(Nat.ble ps.1 i && Nat.blt ps.2 K &&
      Nat.beq (X (Nat.succ i)) (MF (X ps.1) (G ps.2)), ih (Nat.succ i))) par

@[expose] noncomputable def conjF (GA GB : Nat → Nat) (s x : Nat) : Nat := MF (MF (GA s) x) (GB s)

@[expose] noncomputable def wC (w : Nat) : Nat := Nat.land w 65535

@[expose] noncomputable def wP (w s : Nat) : Nat :=
  Nat.land (Nat.shiftRight w (Nat.mul 16 (Nat.succ s))) 65535

@[expose] noncomputable def stepF (X GA GB PP : Nat → Nat) (n h s c p x : Nat) (k : Nat → Bool) :
    Bool :=
  bAnd(Nat.blt h c && Nat.ble p c && Nat.blt p n && Nat.beq (X p) (conjF GA GB s x),
    bIf(Nat.beq p c, bAnd(Nat.beq (PP (Nat.pred c)) (Nat.add (Nat.mul 2 h) s), k (Nat.succ c)),
      k c))

@[expose] noncomputable def ostepF (X GA GB WH PP : Nat → Nat) (n lo m hi : Nat) : Bool :=
  allBelow m hi fun j => letB (Nat.add lo j) fun h => letB (WH h) fun w => letB (X h) fun x =>
    stepF X GA GB PP n h 0 (wC w) (wP w 0) x fun c1 =>
      stepF X GA GB PP n h 1 c1 (wP w 1) x fun c2 => Nat.beq (wC (WH (Nat.succ h))) c2

@[expose] noncomputable def powF (c k : Nat) : Nat :=
  nIf(Nat.beq k 0, ONEF, nIf(Nat.beq k 1, c, MF c c))

@[expose] noncomputable def cubeF (c : Nat) : Bool := Nat.beq (MF c (MF c c)) ONEF

@[expose] noncomputable def commF (x y : Nat) : Bool := Nat.beq (MF x y) (MF y x)

@[expose] noncomputable def rtF (B : Nat → Nat) (e : Nat) : Nat :=
  MF (MF (MF (powF (B 0) (Nat.mod e 3)) (powF (B 1) (Nat.mod (Nat.div e 3) 3)))
    (powF (B 2) (Nat.mod (Nat.div e 9) 3))) (powF (B 3) (Nat.mod (Nat.div e 27) 3))

@[expose] noncomputable def memF (p : Nat) (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun a _ ih => bIf(Nat.beq a p, true, ih)) l

@[expose] noncomputable def basF (X : Nat → Nat) (a : Nat) : Nat := X (uLiftBasis.getD a 0)

@[expose] noncomputable def rtK (X RTP RTI : Nat → Nat) : Bool :=
  allBelow 4 1 (fun a => allBelow 4 1 fun b => commF (basF X a) (basF X b)) &&
  allBelow 4 1 (fun a => cubeF (basF X a)) &&
  allBelow 81 2 fun e => letB (RTP e) fun r =>
    Nat.blt r 729 && memF r uRt && Nat.beq (RTI r) e && Nat.beq (X r) (rtF (basF X) e)

@[expose] noncomputable def wconjF (A : Nat → Nat) (w : List Nat) (x : Nat) : Nat :=
  MF (MF (wordF A w) x) (wordF A (invWord w))

@[expose] noncomputable def kindF (X A : Nat → Nat) (b : Nat) (ks : List Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun k _ ih p => bAnd(bIf(Nat.beq k 3,
      wordOK (convDWord p) && Nat.beq (wconjF A (convDWord p) (X p)) b, true), ih (Nat.succ p))) ks

@[expose] noncomputable def zF (X : Nat → Nat) (z : Nat) : Bool :=
  !(Nat.beq z ONEF) && cubeF z && allBelow 729 12 fun q => commF (X q) z

@[expose] noncomputable def centN (X : Nat → Nat) (b : Nat) : Nat :=
  sumBelow 729 12 fun q => nIf(commF (X q) b, 1, 0)

@[expose] noncomputable def centF (X : Nat → Nat) (b : Nat) : Bool :=
  cubeF b && Nat.beq (centN X b) 81

end CFSG.KD.U43

end
