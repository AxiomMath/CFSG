module

public import Certificates.Data.Kernel.SporSch.HNXT4

public section

namespace CFSG.KC.LL.HNXSyl

open CFSG.KC.Enum CFSG.KC.LL CFSG.KC.LL.HNX

@[expose] noncomputable def f14 (P j : Nat) : Nat := fldW P (Nat.mul (nat_lit 14) j) (nat_lit 14)

@[expose] noncomputable def rowK (SG R PAR LAB : Nat → Nat) (len i : Nat) : Bool :=
  strictB (R i) fun v => strictB (R (PAR i)) fun vp => strictB (SG (LAB i)) fun s =>
    allN len fun k => Nat.beq (f14 v k) (f14 s (f14 vp k))

@[expose] noncomputable def imgK (SG R : Nat → Nat) (len j a b : Nat) : Bool :=
  strictB (R a) fun va => strictB (R b) fun vb => strictB (SG j) fun s =>
    allN len fun k => Nat.beq (f14 va k) (f14 s (f14 vb k))

@[expose] noncomputable def blockK (SG V W : Nat → Nat) (len j a b : Nat) : Bool :=
  strictB (V a) fun va => strictB (W b) fun wb => strictB (SG j) fun s =>
    allN len fun k => Nat.beq (f14 va k) (f14 s (f14 wb (Nat.add (Nat.mul len j) k)))

@[expose] noncomputable def emat (GM PAR LAB : Nat → Nat) (f : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun _ => CFSG.KD.OrdHN.ONE)
    (fun _ ih i => nIf(Nat.beq i (nat_lit 0), CFSG.KD.OrdHN.ONE,
      CFSG.KC.LL.HN.mm (GM (LAB i)) (ih (PAR i)))) f

@[expose] noncomputable def memL (l : List Nat) (x : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun a _ ih => bIf(Nat.beq a x, true, ih)) l

end CFSG.KC.LL.HNXSyl

end
