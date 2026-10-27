module

public import Certificates.Data.Kernel.Spor.PEnum

public section

namespace CFSG.KS.McLNT

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.PEnum

@[expose] noncomputable def pc (p q : Nat) : Nat := pcomp 275 9 (mask 9) p q

@[expose] noncomputable def idP : Nat := pidn 275 9

@[expose] noncomputable def pwK (e x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) idP (fun _ acc => strictN acc (fun a => pc x a)) e

@[expose] noncomputable def witK (G GI X A AI e m : Nat) : Bool :=
  strictB (pc G (pc X GI)) (fun y =>
  strictB (pc y (pc A (pc y AI))) (fun z =>
  strictB (pwK e z) (fun v =>
    bAnd(bIf(Nat.beq v idP, false, true),
    bAnd(Nat.beq (pwK m v) idP,
      bIf(Nat.beq (Nat.mod m (nat_lit 3)) (nat_lit 0), false, true))))))

@[expose] noncomputable def ntItemK (G GI XA XE ST SI W : Nat → Nat) (j i : Nat) : Bool :=
  strictB (r32 W (Nat.add (Nat.mul j (nat_lit 1232)) i)) (fun v =>
  strictB (Nat.land v (nat_lit 255)) (fun a =>
    bAnd(Nat.blt a (nat_lit 128),
      witK (G j) (GI j) (nIf(Nat.blt i (nat_lit 112), XA i, XE (Nat.sub i (nat_lit 112))))
        (ST a) (SI a) (Nat.land (Nat.shiftRight v (nat_lit 8)) (nat_lit 255))
        (Nat.shiftRight v (nat_lit 16)))))

end CFSG.KS.McLNT

end
