module

public import Certificates.Data.Kernel.Spor.FpBfs

public section

namespace CFSG.KS.CEnum

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.FpBfs

@[expose] noncomputable def cKey (w m Rho t ti : Nat) : Nat :=
  fpOf (fun x => pg w m t (pg w m Rho (pg w m ti x)))

@[expose] noncomputable def cKeyS (w m Rho g gi t ti : Nat) : Nat :=
  fpOf (fun x => pg w m g (pg w m t (pg w m Rho (pg w m ti (pg w m gi x)))))

@[expose] noncomputable def cenumHdK (n w m nw k cnt R Rho : Nat) (G GI T FP : Nat → Nat) :
    Bool :=
  bAnd(Nat.blt (nat_lit 0) k, bAnd(Nat.blt (nat_lit 0) cnt,
  bAnd(Nat.beq (T (nat_lit 0)) R, bAnd(canonK n w m nw Rho,
  bAnd(Nat.beq (FP (nat_lit 0)) (fpK w m Rho),
    allN k (fun s => bAnd(canonK n w m nw (G s), bAnd(canonK n w m nw (GI s),
      permOK n w m nw (G s) (GI s)))))))))

@[expose] noncomputable def cenumPtK (n w m nw k cnt Rho : Nat)
    (G GI T TI PL POS FP SRT SRI : Nat → Nat) (i : Nat) : Bool :=
  strictB (T i) (fun t => strictB (TI i) (fun ti =>
  bAnd(canonK n w m nw t, bAnd(canonK n w m nw ti,
  bAnd(permOK n w m nw t ti, bAnd(Nat.beq (FP i) (cKey w m Rho t ti),
  bAnd(bIf(Nat.beq i (nat_lit 0), true, strictB (PL i) (fun c =>
    bAnd(Nat.blt (Nat.div c k) i,
    bAnd(Nat.beq t (pcomp n w m (G (Nat.mod c k)) (T (Nat.div c k))),
      bIf(Nat.blt (Nat.succ i) cnt, Nat.blt c (PL (Nat.succ i)), true))))),
  bAnd(allN k (fun s => strictB (POS (Nat.add (Nat.mul k i) s)) (fun q =>
    bAnd(Nat.blt q cnt, bAnd(Nat.beq (FP q) (cKeyS w m Rho (G s) (GI s) t ti),
      bIf(Nat.beq q (nat_lit 0), true, Nat.ble (PL q) (Nat.add (Nat.mul k i) s)))))),
  bAnd(strictB (SRI i) (fun r => bAnd(Nat.blt r cnt, Nat.beq (SRT r) i)),
  strictB (SRT i) (fun r => bAnd(Nat.blt r cnt, bAnd(Nat.beq (SRI r) i,
    bIf(Nat.blt (Nat.succ i) cnt, Nat.blt (FP r) (FP (SRT (Nat.succ i))), true)))))))))))))

@[expose] noncomputable def cenumSlK (n w m nw k cnt Rho : Nat)
    (G GI T TI PL POS FP SRT SRI : Nat → Nat) (lo len : Nat) : Bool :=
  allN len (fun d => strictB (Nat.add lo d) (fun i =>
    bIf(Nat.blt i cnt, cenumPtK n w m nw k cnt Rho G GI T TI PL POS FP SRT SRI i, true)))

end CFSG.KS.CEnum

end
