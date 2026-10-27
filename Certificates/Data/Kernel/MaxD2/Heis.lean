module

public import Certificates.Data.Kernel.MaxD2.Check

public section

namespace CFSG.KS.MaxD2

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Row CFSG.KS.PEnum

@[expose] noncomputable def commUVK (n w U V x : Nat) : Bool :=
  bAnd(Nat.beq (pcomp n w (mask w) x U) (pcomp n w (mask w) U x),
    Nat.beq (pcomp n w (mask w) x V) (pcomp n w (mask w) V x))

@[expose] noncomputable def zK (n w rcnt nz : Nat) (RT ZP ZX : Nat → Nat) (U V : Nat) : Bool :=
  bAnd(allN rcnt (fun r => strictB (ZX r) (fun x =>
      bIf(commUVK n w U V (RT r),
        bAnd(Nat.blt 0 x, bAnd(Nat.ble x nz, Nat.beq (ZP (Nat.sub x 1)) r)),
        Nat.beq x 0))),
    allN nz (fun j => strictB (ZP j) (fun r => bAnd(Nat.blt r rcnt, Nat.beq (ZX r) (Nat.succ j)))))

@[expose] noncomputable def commK (n w rcnt nz : Nat) (RT ZP CZ : Nat → Nat) (k l : Nat) : Bool :=
  strictB (RT k) (fun x => strictB (RT l) (fun y =>
    strictB (pcomp n w (mask w) x y) (fun xy => strictB (pcomp n w (mask w) y x) (fun yx =>
      strictB (CZ (Nat.add (Nat.mul rcnt k) l)) (fun a =>
        strictB (CZ (Nat.add (Nat.mul rcnt l) k)) (fun b =>
          bAnd(Nat.blt a nz, bAnd(Nat.blt b nz,
            bAnd(Nat.beq xy (pcomp n w (mask w) (RT (ZP a)) yx),
              Nat.beq yx (pcomp n w (mask w) (RT (ZP b)) xy))))))))))

@[expose] noncomputable def anyZ (nz : Nat) (RT ZP : Nat → Nat) (f : Nat → Bool) : Bool :=
  bIf(allN nz (fun j => bIf(f (RT (ZP j)), false, true)), false, true)

@[expose] noncomputable def torusHK (n w p rcnt nz tm tlam te : Nat) (RT ZP : Nat → Nat)
    (U V t ti : Nat) : Bool :=
  bAnd(strictB (pw n w t tm) (fun a => strictB (pw n w ti tm) (fun ai =>
      allN rcnt (fun k => strictB (RT k) (fun r =>
        strictB (pcomp n w (mask w) (pcomp n w (mask w) a r) ai) (fun y =>
          strictB (pw n w r tlam) (fun xl =>
            anyZ nz RT ZP (fun z => Nat.beq y (pcomp n w (mask w) xl z)))))))),
    bAnd(strictB (pw n w t te) (fun a => strictB (pw n w ti te) (fun ai =>
      allN rcnt (fun k => strictB (RT k) (fun r =>
        strictB (pcomp n w (mask w) (pcomp n w (mask w) (pcomp n w (mask w) a r) ai) r) (fun y =>
          anyZ nz RT ZP (fun z => Nat.beq y z)))))),
    allN (Nat.sub tm (nat_lit 1)) (fun k => strictB (pw n w t (Nat.succ k)) (fun a =>
      strictB (pw n w ti (Nat.succ k)) (fun ai =>
      allN rcnt (fun i => strictB (RT i) (fun r =>
        bIf(commUVK n w U V r, true,
          strictB (pcomp n w (mask w) (pcomp n w (mask w) a r) ai) (fun y =>
            allN p (fun j => strictB (pw n w r j) (fun xj =>
              allN nz (fun l => bIf(Nat.beq y (pcomp n w (mask w) xj (RT (ZP l))), false,
                true)))))))))))))

@[expose] noncomputable def selK (nr np2 : Nat) (MK CN PQ PI PJ : Nat → Nat) : Bool :=
  allN nr (fun j => allN j (fun i =>
    bIf(Nat.beq (MK i) (MK j),
      bIf(Nat.beq (CN i) (CN j),
        strictB (PQ (Nat.add (Nat.div (Nat.mul j (Nat.sub j 1)) 2) i)) (fun q =>
          bAnd(Nat.blt q np2, bAnd(Nat.beq (PI q) i, Nat.beq (PJ q) j))),
        true),
      true)))

end CFSG.KS.MaxD2

end
