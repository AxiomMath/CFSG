module

public import Certificates.Data.Kernel.Spor.Prim

public section

namespace CFSG.KS.Ivk8Cent

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim

@[expose] noncomputable def pc (n w p q : Nat) : Nat := pcomp n w (mask w) p q

@[expose] noncomputable def evW (n w : Nat) (L : Nat → Nat) (ws : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (pidn n w)
    (fun l _ ih => strictN ih (fun r => pc n w (L l) r)) ws

@[expose] noncomputable def cube (n w u : Nat) : Nat := strictN (pc n w u u) (fun s => pc n w u s)

@[expose] noncomputable def movesP (n w u : Nat) : Bool :=
  strictB (cube n w u) fun a => strictB (cube n w a) fun b =>
    bIf(Nat.beq (cube n w b) (pidn n w), false, true)

@[expose] noncomputable def wit1P (n w x : Nat) (hs : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false
    (fun a _ ih => bIf(movesP n w (pc n w x (pc n w (pc n w a x) a)), true, ih)) hs

@[expose] noncomputable def wit2In (n w x y : Nat) (hs : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false
    (fun b _ ih => bIf(movesP n w (pc n w y (pc n w (pc n w b x) b)), true, ih)) hs

@[expose] noncomputable def wit2Q (n w x : Nat) (as hs : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false
    (fun a _ ih => bIf(strictB (pc n w x (pc n w (pc n w a x) a)) (fun y => wit2In n w x y hs),
      true, ih)) as

@[expose] noncomputable def wit2P (n w x : Nat) (hs : List Nat) : Bool := wit2Q n w x hs hs

@[expose] noncomputable def chkKP (n w c ci cnt : Nat) (T : Nat → Nat) (hs : List Nat) : Bool :=
  allN cnt (fun i => strictB (pc n w c (pc n w (T i) ci)) (fun x =>
    bIf(wit1P n w x hs, true, wit2P n w x hs)))

@[expose] noncomputable def withH (n w : Nat) (L : Nat → Nat) (wA wB wC : List Nat)
    (k : Nat → Nat → Nat → List Nat → Bool) : Bool :=
  strictB (evW n w L wA) fun A => strictB (evW n w L wB) fun B => strictB (evW n w L wC) fun C =>
  strictB (pc n w A B) fun AB => strictB (pc n w A C) fun AC => strictB (pc n w B C) fun BC =>
  strictB (pc n w AB C) fun ABC => k C AB ABC [A, B, AB, C, AC, BC, ABC]

@[expose] noncomputable def neP (p q : Nat) : Bool := bIf(Nat.beq p q, false, true)

@[expose] noncomputable def hOK (n w : Nat) (L : Nat → Nat) (wA wB wC : List Nat) : Bool :=
  strictB (evW n w L wA) fun A => strictB (evW n w L wB) fun B => strictB (evW n w L wC) fun C =>
  strictB (pidn n w) fun e =>
  bAnd(Nat.beq (pc n w A A) e, bAnd(Nat.beq (pc n w B B) e, bAnd(Nat.beq (pc n w C C) e,
  bAnd(Nat.beq (pc n w A B) (pc n w B A), bAnd(Nat.beq (pc n w A C) (pc n w C A),
  bAnd(Nat.beq (pc n w B C) (pc n w C B), bAnd(neP C e, bAnd(neP (pc n w A B) e,
    neP C (pc n w A B)))))))))

@[expose] noncomputable def conjOK (n w c ci t e : Nat) : Bool :=
  bAnd(Nat.beq (pc n w c ci) (pidn n w), Nat.beq (pc n w c (pc n w t ci)) e)

end CFSG.KS.Ivk8Cent

end
