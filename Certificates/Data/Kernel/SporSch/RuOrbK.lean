module

public import Certificates.Data.Kernel.Spor.Raw
public import Certificates.Data.Kernel.Misc.RuInv

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.RuInv

@[expose] noncomputable def labK (n w K : Nat) (L SZ POS : Nat → Nat) (LAB : Nat) : Bool :=
  bAnd(allN K (fun k => allN (SZ k) (fun i => strictB (pg w (mask w) (L k) i) (fun x =>
      bAnd(Nat.blt x n, Nat.beq (pg w (mask w) LAB x) k)))),
    allN n (fun x => strictB (pg w (mask w) LAB x) (fun c => bAnd(Nat.blt c K,
      strictB (pg w (mask w) (POS c) x) (fun p =>
        bAnd(Nat.blt p (SZ c), Nat.beq (pg w (mask w) (L c) p) x))))))

@[expose] noncomputable def gimg (w G0 G1 k x : Nat) : Nat := pg w (mask w) (gen2 G0 G1 k) x

@[expose] noncomputable def forestAt (n w wf R G0 G1 Q ORD FO DEP PAR GL t : Nat) : Bool :=
  strictB (pg w (mask w) Q t) (fun q => bAnd(Nat.blt q n, bAnd(Nat.beq (pg w (mask w) ORD q) t,
    bIf(Nat.blt t R,
      bAnd(Nat.beq (pg w (mask w) DEP q) 0, bAnd(Nat.beq (pg w (mask w) PAR q) 0,
        Nat.beq (pg w (mask w) GL q) 0)),
      strictB (pg wf (mask wf) FO t) (fun f => strictB (Nat.div f 2) (fun h =>
        strictB (Nat.mod f 2) (fun k => strictB (pg w (mask w) Q h) (fun p =>
          bAnd(Nat.blt h t, bAnd(Nat.beq (gimg w G0 G1 k p) q,
          bAnd(Nat.beq (pg w (mask w) PAR q) p, bAnd(Nat.beq (pg w (mask w) GL q) k,
          bAnd(Nat.beq (pg w (mask w) DEP q) (Nat.succ (pg w (mask w) DEP p)),
            bIf(Nat.blt (Nat.succ t) n, Nat.blt f (pg wf (mask wf) FO (Nat.succ t)), true))))))))))))))

@[expose] noncomputable def eventAt (n w wf R G0 G1 Q ORD FO e : Nat) : Bool :=
  strictB (gimg w G0 G1 (Nat.mod e 2) (pg w (mask w) Q (Nat.div e 2))) (fun y =>
    bAnd(Nat.blt y n, strictB (pg w (mask w) ORD y) (fun t =>
      bIf(Nat.blt t R, true, Nat.ble (pg wf (mask wf) FO t) e))))

@[expose] noncomputable def partAt (n w R G0 G1 LAB Q DEP PAR GL x : Nat) : Bool :=
  strictB (pg w (mask w) LAB x) (fun c =>
    bAnd(strictB (gimg w G0 G1 0 x) (fun y => bAnd(Nat.blt y n, Nat.beq (pg w (mask w) LAB y) c)),
    bAnd(strictB (gimg w G0 G1 1 x) (fun y => bAnd(Nat.blt y n, Nat.beq (pg w (mask w) LAB y) c)),
      bIf(Nat.beq (pg w (mask w) DEP x) 0,
        bAnd(Nat.blt c R, Nat.beq (pg w (mask w) Q c) x),
        strictB (pg w (mask w) PAR x) (fun p => strictB (pg w (mask w) GL x) (fun g =>
          bAnd(Nat.blt p n, bAnd(Nat.blt (pg w (mask w) DEP p) (pg w (mask w) DEP x),
            bAnd(Nat.blt g 2, Nat.beq (gimg w G0 G1 g p) x)))))))))

@[expose] noncomputable def rootAt (n w LAB Q k : Nat) : Bool :=
  strictB (pg w (mask w) Q k) (fun r => bAnd(Nat.blt r n, Nat.beq (pg w (mask w) LAB r) k))

end CFSG.KS.SporSch

end
