module

public import Certificates.Data.Kernel.SporSch.HNXPt
public import Certificates.Data.Kernel.SporSch.HNXPrim
public import Certificates.Data.Kernel.Spor.PEnum

public section

namespace CFSG.KC.LL.HNXT4

open CFSG.KC.Enum CFSG.KC.LL CFSG.KC.LL.HNX CFSG.KS.PEnum

@[expose] noncomputable def f21 (P j : Nat) : Nat := fldW P (Nat.mul (nat_lit 21) j) (nat_lit 21)

@[expose] noncomputable def chunkK (T : Nat → Nat) (MS CM3 M : Nat) (MX FL IL MI NC : Nat → Nat)
    (c : Nat) : Bool :=
  bAnd(Nat.ble (NC c) (nat_lit 64),
    bAnd(allN (NC c) (fun i => bAnd(Nat.blt (f21 (FL c) i) (nat_lit 1140000),
      Nat.blt (f21 (IL c) i) (nat_lit 1140000))),
    ptsImg T MS CM3 M (trM (MX (MI c))) (FL c) (IL c) (NC c)))

@[expose] noncomputable def stepK (FL IL MI NC : Nat → Nat) (nch s m x y : Nat) : Bool :=
  strictB (Nat.shiftRight s (nat_lit 6)) fun c => strictB (Nat.land s (nat_lit 63)) fun i =>
    bAnd(Nat.blt c nch, bAnd(Nat.blt i (NC c), bAnd(Nat.beq (MI c) m,
      bAnd(Nat.beq (f21 (FL c) i) x, Nat.beq (f21 (IL c) i) y))))

@[expose] noncomputable def factK (PL FL IL MI NC : Nat → Nat) (nch FR FX FY FP FS j : Nat) : Bool :=
  strictB (f21 FR j) fun r => strictB (f21 FX j) fun x => strictB (f21 FY j) fun y =>
    bAnd(Nat.blt r (nat_lit 16384), bAnd(Nat.blt x (nat_lit 1140000),
      bAnd(Nat.blt y (nat_lit 1140000),
        bIf(Nat.beq r (nat_lit 0), Nat.beq y x,
          strictB (f21 FP j) fun p =>
            bAnd(Nat.blt p j, bAnd(Nat.beq (f21 FR p) (parOf PL r), bAnd(Nat.beq (f21 FX p) x,
              stepK FL IL MI NC nch (f21 FS j) (labOf PL r) (f21 FY p) y)))))))

@[expose] noncomputable def faithK (FL IL MI NC : Nat → Nat) (nch nf FR FX FY AK AF AQ AS AB a : Nat) :
    Bool :=
  strictB (f21 AK a) fun k => strictB (f21 AF a) fun f =>
    bAnd(Nat.blt f (nat_lit 9),
      bAnd(allN (nat_lit 4) (fun i =>
        strictB (f21 AQ (Nat.add (Nat.mul (nat_lit 9) a) (Nat.mul (nat_lit 2) i))) fun q0 =>
        strictB (f21 AQ (Nat.add (Nat.add (Nat.mul (nat_lit 9) a) (Nat.mul (nat_lit 2) i))
          (nat_lit 1))) fun q1 =>
        strictB (f21 AQ (Nat.add (Nat.add (Nat.mul (nat_lit 9) a) (Nat.mul (nat_lit 2) i))
          (nat_lit 2))) fun q2 =>
        strictB (f21 AB (Nat.add (Nat.mul (nat_lit 4) a) i)) fun b =>
          bAnd(stepK FL IL MI NC nch (f21 AS (Nat.add (Nat.mul (nat_lit 4) a) i))
              (nIf(Nat.beq (Nat.land i (nat_lit 1)) (nat_lit 0), Nat.add (nat_lit 23) f,
                Nat.add (nat_lit 14) f)) q0 q1,
            bAnd(Nat.blt b nf, bAnd(Nat.beq (f21 FR b) k,
              bAnd(Nat.beq (f21 FX b) q1, Nat.beq (f21 FY b) q2))))),
        Bool.not (Nat.beq (f21 AQ (Nat.add (Nat.mul (nat_lit 9) a) (nat_lit 8)))
          (f21 AQ (Nat.mul (nat_lit 9) a)))))

@[expose] noncomputable def noInvK (nf FR FX FY NK NQ NB a : Nat) : Bool :=
  strictB (f21 NK a) fun k =>
    bAnd(allN (nat_lit 2) (fun i => strictB (f21 NB (Nat.add (Nat.mul (nat_lit 2) a) i)) fun b =>
        bAnd(Nat.blt b nf, bAnd(Nat.beq (f21 FR b) k,
          bAnd(Nat.beq (f21 FX b) (f21 NQ (Nat.add (Nat.mul (nat_lit 3) a) i)),
            Nat.beq (f21 FY b) (f21 NQ (Nat.add (Nat.add (Nat.mul (nat_lit 3) a) i) (nat_lit 1))))))),
      Bool.not (Nat.beq (f21 NQ (Nat.add (Nat.mul (nat_lit 3) a) (nat_lit 2)))
        (f21 NQ (Nat.mul (nat_lit 3) a))))

@[expose] noncomputable def eqNL : List Nat → List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool)
    (fun m => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) m)
    (fun a _ ih m => List.rec (motive := fun _ => Bool) false (fun b t _ => bAnd(Nat.beq a b, ih t)) m)

@[expose] noncomputable def mapK (WN WP : Nat → Nat) (na ni AK AF AQ NK NQ TK k : Nat) : Bool :=
  strictB (WP k) fun s => strictB (WN s) fun c => strictB (f21 TK k) fun t =>
    bIf(Nat.beq c (nat_lit 2),
      bAnd(Nat.blt t na, bAnd(Nat.beq (f21 AK t) k, bAnd(Nat.beq (f21 AF t) (WN (Nat.succ s)),
        Nat.beq (f21 AQ (Nat.mul (nat_lit 9) t)) (WN (Nat.add s (nat_lit 2)))))),
    bIf(Nat.beq c (nat_lit 3),
      bAnd(Nat.blt t ni, bAnd(Nat.beq (f21 NK t) k,
        Nat.beq (f21 NQ (Nat.mul (nat_lit 3) t)) (WN (Nat.succ s)))), true))

end CFSG.KC.LL.HNXT4

end
