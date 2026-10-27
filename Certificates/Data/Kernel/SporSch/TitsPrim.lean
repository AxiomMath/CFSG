module

public import Certificates.Data.Kernel.SporSch.TitsStab

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.Mathieu

@[expose] noncomputable def scanK (w : Nat) (GS : Nat → Nat) (POS LAB DEP PAR GL x c' : Nat) :
    Nat → Nat → Nat → Bool :=
  fun f => Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ c => Nat.beq c c')
    (fun _ ih i c => strictB (pgW w (GS i) x) (fun y => strictB (pgW w POS y) (fun py =>
      bIf(Nat.ble c py,
        bAnd(Nat.beq py c, bAnd(Nat.beq (pgW w LAB y) (pgW w LAB x),
          bAnd(Nat.beq (pgW w DEP y) (Nat.succ (pgW w DEP x)), bAnd(Nat.beq (pgW w PAR y) x,
          bAnd(Nat.beq (pgW w GL y) i, ih (Nat.succ i) (Nat.succ c)))))),
        ih (Nat.succ i) c)))) f

@[expose] noncomputable def bfsTK (n w : Nat) (GS : Nat → Nat) (kG m REP N Q POS C LAB DEP PAR GL :
    Nat) : Bool :=
  bAnd(Nat.ble m N, bAnd(Nat.ble N n, bAnd(Nat.beq (pgW w C 0) m, bAnd(Nat.beq (pgW w C N) N,
  bAnd(allN m (fun c => strictB (pgW w REP c) (fun r => bAnd(Nat.beq (pgW w Q c) r,
    bAnd(Nat.beq (pgW w LAB r) c, bAnd(Nat.beq (pgW w DEP r) 0,
      bAnd(Nat.beq (pgW w PAR r) 0, Nat.beq (pgW w GL r) 0)))))),
  bAnd(allN N (fun k => strictB (pgW w Q k) (fun y => bAnd(Nat.blt y n, Nat.beq (pgW w POS y) k))),
  bAnd(allN n (fun y => strictB (pgW w POS y) (fun py => bIf(Nat.blt py N,
    Nat.beq (pgW w Q py) y,
    bAnd(Nat.beq (pgW w LAB y) m, bAnd(Nat.beq (pgW w DEP y) 0,
      bAnd(Nat.beq (pgW w PAR y) 0, Nat.beq (pgW w GL y) 0)))))),
  allN N (fun h => scanK w GS POS LAB DEP PAR GL (pgW w Q h) (pgW w C (Nat.succ h)) kG 0
    (pgW w C h)))))))))

@[expose] noncomputable def labOKK (n w : Nat) (GS : Nat → Nat) (kG m LAB REP DEP PAR GL : Nat) :
    Bool :=
  bAnd(allN n (fun x => Nat.blt (pgW w LAB x) m),
  bAnd(allN kG (fun i => allN n (fun x => Nat.beq (pgW w LAB (pgW w (GS i) x)) (pgW w LAB x))),
  bAnd(allN m (fun c => strictB (pgW w REP c) (fun r => bAnd(Nat.blt r n,
    bAnd(Nat.beq (pgW w LAB r) c, Nat.beq (pgW w DEP r) 0)))),
  allN n (fun x => bIf(bAnd(Nat.beq (pgW w DEP x) 0, Nat.beq (pgW w REP (pgW w LAB x)) x), true,
    strictB (pgW w PAR x) (fun p => strictB (pgW w GL x) (fun g =>
    bAnd(Nat.blt 0 (pgW w DEP x), bAnd(Nat.blt p n, bAnd(Nat.beq (Nat.succ (pgW w DEP p))
      (pgW w DEP x), bAnd(Nat.blt g kG, Nat.beq (pgW w (GS g) p) x)))))))))))

@[expose] noncomputable def cntK (n w LAB c : Nat) : Nat :=
  foldN n (fun x s => nIf(Nat.beq (pgW w LAB x) c, Nat.succ s, s)) 0

@[expose] noncomputable def findK (n w TP PP k : Nat) (fuel l : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun _ => n)
    (fun _ ih l => nIf(Nat.blt (pgW 12 TP l) k, ih (pgW w PP l), l)) fuel l

@[expose] noncomputable def isRoot (n TP k r : Nat) : Bool :=
  bAnd(Nat.blt r n, bIf(Nat.blt (pgW 12 TP r) k, false, true))

@[expose] noncomputable def rootC (n w S TP PP : Nat) (A : Nat → Nat) (s k y : Nat) : Nat :=
  findK n w TP PP k (Nat.succ S) (pgW w (A s) y)

@[expose] noncomputable def mergedC (n w : Nat) (GS : Nat → Nat) (S TP PP : Nat) (A : Nat → Nat)
    (s k i u v : Nat) : Nat :=
  nIf(Nat.beq (rootC n w S TP PP A s k (pgW w (GS i) v)) (rootC n w S TP PP A s k (pgW w (GS i) u)),
    0, 1)

@[expose] noncomputable def mergeCnt (n w : Nat) (GS : Nat → Nat) (Lc S TP PP : Nat)
    (A RI RU RV : Nat → Nat) : Nat :=
  foldN Lc (fun k c => Nat.add c (mergedC n w GS S TP PP A (Nat.div k S) k (RI k) (RU k) (RV k))) 0

@[expose] noncomputable def timedCnt (n Lc TP : Nat) : Nat :=
  foldN n (fun l c => nIf(Nat.blt (pgW 12 TP l) Lc, Nat.succ c, c)) 0

@[expose] noncomputable def finalC (n w Lc NS TP : Nat) (A : Nat → Nat) : Bool :=
  strictB (pgW w (A NS) 0) (fun r0 => bAnd(isRoot n TP Lc r0,
    allN n (fun a => Nat.beq (pgW w (A NS) a) r0)))

@[expose] noncomputable def digK (D : Nat → Nat) (o : Nat) : Nat :=
  pg 4 (mask 4) (D (Nat.div o 623)) (Nat.mod o 623)

@[expose] noncomputable def hex3K (D : Nat → Nat) (o : Nat) : Nat :=
  Nat.add (Nat.mul (Nat.add (Nat.mul (digK D o) 16) (digK D (Nat.succ o))) 16)
    (digK D (Nat.add o 2))

end CFSG.KS.SporSch

end
