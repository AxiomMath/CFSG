module

public import Certificates.Data.Kernel.SporSch.Co1GenK

public section

namespace CFSG.KS.SporSch.VOrb

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch.M24 CFSG.KS.Mathieu

@[expose] noncomputable def lnB (B e : Nat) : Nat := fld(B, Nat.mul (nat_lit 24) e, nat_lit 16777215)

@[expose] noncomputable def actN (B v : Nat) : Nat :=
  Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor
    (lnB B (Nat.add (nat_lit 0) (Nat.land (Nat.shiftRight v (nat_lit 0)) (nat_lit 15))))
    (lnB B (Nat.add (nat_lit 16) (Nat.land (Nat.shiftRight v (nat_lit 4)) (nat_lit 15)))))
    (lnB B (Nat.add (nat_lit 32) (Nat.land (Nat.shiftRight v (nat_lit 8)) (nat_lit 15)))))
    (lnB B (Nat.add (nat_lit 48) (Nat.land (Nat.shiftRight v (nat_lit 12)) (nat_lit 15)))))
    (lnB B (Nat.add (nat_lit 64) (Nat.land (Nat.shiftRight v (nat_lit 16)) (nat_lit 15)))))
    (lnB B (Nat.add (nat_lit 80) (Nat.land (Nat.shiftRight v (nat_lit 20)) (nat_lit 15))))

@[expose] noncomputable def tabOK (X B : Nat) : Bool :=
  allN (nat_lit 96) (fun e => Nat.beq (lnB B e)
    (actK X (Nat.shiftLeft (Nat.land e (nat_lit 15)) (Nat.mul (nat_lit 4) (Nat.shiftRight e (nat_lit 4))))))

@[expose] noncomputable def actS (M B : Nat → Nat) (g v : Nat) : Nat :=
  nIf(Nat.blt g (nat_lit 93), actN (B g) v, actK (M g) v)

@[expose] noncomputable def lvlGensA (A : Nat → Nat → Nat) (T E : Nat → Nat) (q G h v : Nat) :
    List Nat → Nat → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat) (fun _ c => c)
    (fun g _ ih p c => nIf(Nat.blt c failC,
      strictN (eK17 E (Nat.add (Nat.mul h G) p)) (fun e =>
      strictN (canonK q (A g v)) (fun w =>
        nIf(bAnd(Nat.ble e c, Nat.beq (ptK T e) w),
          nIf(Nat.beq e c,
            nIf(bAnd(Nat.beq (parK T e) h, Nat.beq (genK T e) g), ih (Nat.succ p) (Nat.succ c), failC),
            ih (Nat.succ p) c),
          failC))), failC))

@[expose] noncomputable def levelSlA (A : Nat → Nat → Nat) (q : Nat) (gens : List Nat) (n : Nat)
    (T E : Nat → Nat) (lo len c₀ c₁ : Nat) : Bool :=
  strictB (lenN gens) (fun G =>
    Nat.beq (foldUp len (fun d c => strictN (Nat.add lo d) (fun h =>
      nIf(Nat.blt c failC, nIf(Nat.blt h n, nIf(Nat.blt h c,
        strictN (ptK T h) (fun v => nIf(Nat.beq (canonK q v) v,
          lvlGensA A T E q G h v gens (nat_lit 0) c, failC)), failC), c), failC)))
      c₀) c₁)

end CFSG.KS.SporSch.VOrb

end
