module

public import Certificates.Data.Kernel.Co2Cls

public section

namespace CFSG.KC.Co2Fuse

open CFSG.KC.Loop CFSG.KC.Co2InvS CFSG.KC.Co2Cls

@[expose] noncomputable def kS (c : Nat) : Nat := fld(c, nat_lit 484, nat_lit 31)

@[expose] noncomputable def aS (c : Nat) : Nat := fld(c, nat_lit 489, nat_lit 255)

@[expose] noncomputable def rkS (M c : Nat) : Bool :=
  rankL M (elemOf c) (mulV (elemOf c) M) (kS c)

@[expose] noncomputable def orF (a b : Bool) : Bool := bIf(a, true, b)

@[expose] noncomputable def lab10 (CA : Nat → Nat) (R Y s : Nat) : Nat :=
  strictN (CA (Nat.add s (nat_lit 1))) fun c1 => strictN (CA (Nat.add s (nat_lit 2))) fun c2 =>
    selN (andK (rkS (Nat.xor (mulV Y R) IDP) c1) (rkS (mulV (Nat.xor R IDP) (Nat.xor Y IDP)) c2))
      (selN (andK (Nat.beq (kS c1) (nat_lit 10)) (Nat.beq (kS c2) (nat_lit 3))) (nat_lit 4)
        (nat_lit 3))
      (nat_lit 5)

@[expose] noncomputable def labY (CA : Nat → Nat) (R Y s : Nat) : Nat :=
  selN (involK Y)
    (strictN (CA s) fun c =>
      selN (rkS (Nat.xor Y IDP) c)
        (strictN (kS c) fun a =>
          selN (Nat.beq a (nat_lit 6)) (nat_lit 1) (selN (Nat.beq a (nat_lit 8)) (nat_lit 2)
            (selN (Nat.beq a (nat_lit 10)) (lab10 CA R Y s) (nat_lit 5))))
        (nat_lit 5))
    (nat_lit 0)

@[expose] noncomputable def BADF : Nat := nat_lit 1073741824

@[expose] noncomputable def tripC (lY lZ : Nat) : Nat :=
  selN (orF (orF (Nat.beq lY (nat_lit 5)) (Nat.beq lZ (nat_lit 5)))
      (andK (Nat.beq lY (nat_lit 4)) (Nat.beq lZ (nat_lit 3)))) BADF
    (Nat.add (selN (andK (Nat.beq lY (nat_lit 3)) (Nat.beq lZ (nat_lit 4))) (nat_lit 1) (nat_lit 0))
      (Nat.add (selN (andK (Nat.beq lY (nat_lit 3))
          (orF (Nat.beq lZ (nat_lit 2)) (Nat.beq lZ (nat_lit 4)))) (nat_lit 256) (nat_lit 0))
        (selN (andK (orF (Nat.beq lY (nat_lit 2)) (Nat.beq lY (nat_lit 4))) (Nat.beq lZ (nat_lit 3)))
          (nat_lit 65536) (nat_lit 0))))

@[expose] noncomputable def contribA (CA : Nat → Nat) (R S X m : Nat) : Nat :=
  strictN (Nat.mul (nat_lit 6) m) fun s =>
    strictN (labY CA R (mulV X R) s) fun lY =>
      strictN (labY CA R (mulV X S) (Nat.add s (nat_lit 3))) fun lZ => tripC lY lZ

@[expose] noncomputable def contribF (CF PT CI CA : Nat → Nat) (R S N k : Nat) : Nat :=
  selN (Nat.blt k N) (strictN (elemAt CF k) fun X =>
    selN (involK X) (strictN (CI (PT k)) fun c =>
      selN (rkS (Nat.xor X IDP) c)
        (selN (Nat.beq (kS c) (nat_lit 6)) (contribA CA R S X (aS c)) (nat_lit 0))
        BADF)
      (nat_lit 0)) (nat_lit 0)

@[expose] noncomputable def fuseSum (CF PT CI CA : Nat → Nat) (R S N b : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Nat.add acc (contribF CF PT CI CA R S N (Nat.add (Nat.mul (nat_lit 64) b) i)))
    (nat_lit 64)

@[expose] noncomputable def fuseB (CF PT CI CA : Nat → Nat) (R S : Nat) (CNT : Nat → Nat)
    (N b : Nat) : Bool :=
  Nat.beq (fuseSum CF PT CI CA R S N b) (cntAt CNT b)

end CFSG.KC.Co2Fuse

end
