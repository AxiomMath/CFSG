module

public import Certificates.Data.Kernel.SporSch.MathieuOC

public section

namespace CFSG.KS.SporSch.ChainCls

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch.MOC

@[expose] noncomputable def cntRK (lo len : Nat) (p : Nat → Bool) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun l ih => strictN ih (fun s => nIf(p (Nat.add lo l), Nat.succ s, s))) len

@[expose] noncomputable def commGK (n w m : Nat) (G : Nat → Nat) (ng x : Nat) : Bool :=
  allN ng (fun i => Nat.beq (pcomp n w m x (G i)) (pcomp n w m (G i) x))

@[expose] noncomputable def commCntK (n w m nw idn : Nat) (LR TR : Nat → Nat) (nb : Nat)
    (G : Nat → Nat) (ng N lo len : Nat) : Nat :=
  cntRK lo len (fun j => bIf(Nat.blt j N,
    strictB (elemK n w m nw idn LR TR nb j) (fun x => commGK n w m G ng x), false))

@[expose] noncomputable def clsInvK (n w m nw idn : Nat) (LR TR : Nat → Nat) (nb : Nat)
    (PS PSI : Nat → Nat) (ng : Nat) (LB CJ RP : Nat → Nat) (c N j : Nat) : Bool :=
  strictB (LB j) (fun l =>
  bAnd(Nat.blt l c, bAnd(Nat.ble j (RP l),
  strictB (elemK n w m nw idn LR TR nb j) (fun x =>
  allN ng (fun g => strictB (CJ (Nat.add (Nat.mul ng j) g)) (fun t =>
    bAnd(Nat.blt t N, bAnd(Nat.beq (LB t) l,
      Nat.beq (elemK n w m nw idn LR TR nb t) (pcomp n w m (PS g) (pcomp n w m x (PSI g)))))))))))

@[expose] noncomputable def clsRepK (n w m nw idn : Nat) (LR TR : Nat → Nat) (nb : Nat)
    (LB RP SZ ZC : Nat → Nat) (N l : Nat) : Bool :=
  strictB (RP l) (fun r =>
  bAnd(Nat.beq (LB r) l, bAnd(Nat.blt r N,
  bAnd(bIf(Nat.beq l (nat_lit 0), true, Nat.blt r (RP (Nat.sub l (nat_lit 1)))),
  bAnd(Nat.beq (Nat.mul (SZ l) (ZC l)) N,
  bAnd(Nat.beq (cntRK (nat_lit 0) N (fun j => Nat.beq (LB j) l)) (SZ l),
  strictB (elemK n w m nw idn LR TR nb r) (fun y =>
    Nat.beq (commCntK n w m nw idn LR TR nb (fun _ => y) (nat_lit 1) N (nat_lit 0) N) (ZC l))))))))

end CFSG.KS.SporSch.ChainCls

end
