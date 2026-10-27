module

public import Certificates.Data.Kernel.Spor.Prim
public import Certificates.Data.Kernel.Spor.Row
public import Certificates.Data.Kernel.Spor.PEnum
public import CFSG.Certificates.Kernel.Common.Loop

public section

namespace CFSG.KS.MaxD2

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Row CFSG.KS.PEnum

@[expose] noncomputable def keyT (w np : Nat) (g : Nat → Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun t acc => Nat.lor acc (Nat.shiftLeft (g t) (Nat.mul w t))) np

@[expose] noncomputable def fpK (w np : Nat) (PT : Nat → Nat) (a : Nat) : Nat :=
  keyT w np (fun t => pg w (mask w) a (PT t))

@[expose] noncomputable def sortK (w np kw cnt : Nat) (PT T FS KS : Nat → Nat) (s : Nat) : Bool :=
  strictB (r32 FS s) (fun e => strictB (rg kw (mask kw) KS (nat_lit 0) s) (fun ks =>
    bAnd(Nat.blt e cnt, bAnd(Nat.beq ks (fpK w np PT (T e)),
      bIf(Nat.blt (Nat.succ s) cnt, Nat.blt ks (rg kw (mask kw) KS (nat_lit 0) (Nat.succ s)),
        true)))))

@[expose] noncomputable def testK (n w np kw cnt : Nat) (T FS KS : Nat → Nat) (RP RPI : Nat)
    (RB : Nat → Nat) (k h : Nat) : Bool :=
  strictB (T k) (fun a =>
    bIf(Nat.beq (Nat.land h (nat_lit 1)) (nat_lit 1),
      strictB (Nat.shiftRight h (nat_lit 1)) (fun e => bAnd(Nat.blt e cnt,
        Nat.beq (pcomp n w (mask w) (pcomp n w (mask w) RPI a) RP) (T e))),
      strictB (keyT w np (fun t => pg w (mask w) RPI (pg w (mask w) a (RB t)))) (fun y =>
        bIf(Nat.beq (Nat.land h (nat_lit 2)) (nat_lit 0),
          strictB (Nat.shiftRight h (nat_lit 2)) (fun q => bAnd(Nat.ble q cnt,
            bAnd(bIf(Nat.beq q (nat_lit 0), true,
                Nat.blt (rg kw (mask kw) KS (nat_lit 0) (Nat.sub q (nat_lit 1))) y),
              bIf(Nat.beq q cnt, true, Nat.blt y (rg kw (mask kw) KS (nat_lit 0) q))))),
          strictB (Nat.land (Nat.shiftRight h (nat_lit 2)) (nat_lit 65535)) (fun s =>
            strictB (Nat.shiftRight h (nat_lit 18)) (fun p =>
            bAnd(Nat.blt s cnt, bAnd(Nat.blt p n,
              bAnd(Nat.beq y (rg kw (mask kw) KS (nat_lit 0) s),
                bIf(Nat.beq (pg w (mask w) RPI (pg w (mask w) a (pg w (mask w) RP p)))
                    (pg w (mask w) (T (r32 FS s)) p), false, true))))))))))

@[expose] noncomputable def repK (n w np kw cnt : Nat) (PT T FS KS REP REPI RB H : Nat → Nat)
    (i : Nat) : Bool :=
  strictB (REP i) (fun rp => strictB (REPI i) (fun rpi =>
    bAnd(allN np (fun t => Nat.beq (r32 RB (Nat.add (Nat.mul np i) t)) (pg w (mask w) rp (PT t))),
      allN cnt (fun k => testK n w np kw cnt T FS KS rp rpi
        (fun t => r32 RB (Nat.add (Nat.mul np i) t)) k (r32 H (Nat.add (Nat.mul cnt i) k))))))

@[expose] noncomputable def posCnt (cnt : Nat) (H : Nat → Nat) (i : Nat) : Nat :=
  foldN cnt (fun k s => Nat.add s (Nat.land (r32 H (Nat.add (Nat.mul cnt i) k)) (nat_lit 1)))
    (nat_lit 0)

@[expose] noncomputable def centK (n w rcnt : Nat) (T RT : Nat → Nat) (U V c k : Nat) : Bool :=
  strictB (T k) (fun a =>
    bIf(Nat.beq (Nat.land c (nat_lit 1)) (nat_lit 1),
      strictB (Nat.shiftRight c (nat_lit 1)) (fun r => bAnd(Nat.blt r rcnt, Nat.beq a (RT r))),
      strictB (Nat.shiftRight c (nat_lit 2)) (fun p =>
        strictB (nIf(Nat.beq (Nat.land (Nat.shiftRight c (nat_lit 1)) (nat_lit 1)) (nat_lit 0), U, V))
          (fun g => bAnd(Nat.blt p n,
            bIf(Nat.beq (pg w (mask w) a (pg w (mask w) g p)) (pg w (mask w) g (pg w (mask w) a p)),
              false, true))))))

@[expose] noncomputable def labK (n w kN : Nat) (G L : Nat → Nat) : Bool :=
  allN kN (fun j => strictB (G j) (fun g =>
    allN n (fun x => Nat.beq (L (pg w (mask w) g x)) (L x))))

@[expose] noncomputable def mkeyK (n w hi cw nl : Nat) (L : Nat → Nat) (g : Nat) : Nat :=
  CFSG.KC.Loop.sumBelow n hi (fun y =>
    Nat.shiftLeft (nat_lit 1) (Nat.mul cw (Nat.add (Nat.mul nl (L (pg w (mask w) g y))) (L y))))

@[expose] noncomputable def conjInK (n w rcnt : Nat) (RT : Nat → Nat) (g gi x h : Nat) : Bool :=
  bAnd(Nat.blt h rcnt, Nat.beq (RT h) (pcomp n w (mask w) (pcomp n w (mask w) g x) gi))

@[expose] noncomputable def notInK (rcnt : Nat) (RT : Nat → Nat) (x : Nat) : Bool :=
  allN rcnt (fun r => bIf(Nat.beq x (RT r), false, true))

@[expose] noncomputable def pw (n w : Nat) (x : Nat) (e : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (pidn n w) (fun _ acc => pcomp n w (mask w) x acc) e

@[expose] noncomputable def torusK (n w p rcnt tm tlam te : Nat) (RT : Nat → Nat) (t ti : Nat) :
    Bool :=
  bAnd(strictB (pw n w t tm) (fun a => strictB (pw n w ti tm) (fun ai =>
      allN rcnt (fun k => strictB (RT k) (fun r =>
        Nat.beq (pcomp n w (mask w) (pcomp n w (mask w) a r) ai) (pw n w r tlam))))),
    bAnd(strictB (pw n w t te) (fun a => strictB (pw n w ti te) (fun ai =>
      allN rcnt (fun k => strictB (RT k) (fun r =>
        Nat.beq (pcomp n w (mask w) (pcomp n w (mask w) (pcomp n w (mask w) a r) ai) r)
          (pidn n w))))),
    allN (Nat.sub tm (nat_lit 1)) (fun k => strictB (pw n w t (Nat.succ k)) (fun a =>
      strictB (pw n w ti (Nat.succ k)) (fun ai =>
      allN rcnt (fun i => strictB (RT i) (fun r =>
        bIf(Nat.beq r (pidn n w), true,
          strictB (pcomp n w (mask w) (pcomp n w (mask w) a r) ai) (fun c =>
            allN p (fun j => bIf(Nat.beq c (pw n w r j), false, true)))))))))))

end CFSG.KS.MaxD2

end
