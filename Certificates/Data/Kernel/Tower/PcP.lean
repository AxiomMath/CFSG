module

public import Certificates.Data.Kernel.Tower.Cls14
public import Certificates.Data.Kernel.Tower.Chi

public section

namespace Certificates.KernelTower

@[expose] noncomputable def pcSel (OT LB RP CZ t x0 l : Nat) : Bool :=
  !(Nat.beq l (lbL LB t) || Nat.beq l (lbL LB x0)) && Nat.beq (oe OT (l16 RP l)) 1 &&
    Nat.beq (lane CZ 15 32767 l) 64

@[expose] noncomputable def pcSL (OT LB RP CZ t x0 nl : Nat) : Nat :=
  Nat.rec 0 (fun l acc => Bool.rec (motive := fun _ => Nat) acc (Nat.add (Nat.mul acc 256) l)
    (pcSel OT LB RP CZ t x0 l)) nl

@[expose] noncomputable def pcK (OT LB RP CZ t x0 nl : Nat) : Nat :=
  cntB nl (pcSel OT LB RP CZ t x0)

@[expose] noncomputable def bitsAt (k : Nat) (p : Nat → Bool) : Nat :=
  Nat.rec 0 (fun j acc => Nat.add acc
    (Bool.rec (motive := fun _ => Nat) 0 (Nat.shiftLeft 1 (Nat.mul 15 j)) (p j))) k

@[expose] noncomputable def cntPI (n k : Nat) (iv : Nat → Bool) (q : Nat → Nat → Bool) : Nat :=
  Nat.rec 0 (fun c acc => Nat.add acc (Bool.rec (motive := fun _ => Nat) 0 (bitsAt k (q c)) (iv c))) n

@[expose] noncomputable def pcC (mul : Nat → Nat → Nat) (RP SL c j : Nat) : Bool :=
  Nat.beq (mul c (l16 RP (lane SL 8 255 j))) (mul (l16 RP (lane SL 8 255 j)) c)

@[expose] noncomputable def pcFin (OT LB RP CZ t x0 nl SL k A : Nat) : Bool :=
  allB nl (fun l => !pcSel OT LB RP CZ t x0 l || anyB k fun j => Nat.beq (lane SL 8 255 j) l) &&
    allB k fun j => !Nat.beq (lane A 15 32767 j) 87

@[expose] noncomputable def pcP (n : Nat) (mul : Nat → Nat → Nat) (OT LB RP CZ nl t x0 : Nat) :
    Bool :=
  pcFin OT LB RP CZ t x0 nl (pcSL OT LB RP CZ t x0 nl) (pcK OT LB RP CZ t x0 nl)
    (cntPI n (pcK OT LB RP CZ t x0 nl) (fun c => Nat.beq (oe OT c) 1)
      (pcC mul RP (pcSL OT LB RP CZ t x0 nl)))

end Certificates.KernelTower
