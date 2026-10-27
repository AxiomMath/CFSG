module

public import Certificates.Data.Kernel.SporSch.PairJ3Cnt
public import Certificates.Data.Kernel.Misc.PermClos

public section

namespace CFSG.KC.HeLoc

open CFSG.KS.SporSch (eqOnL)
open CFSG.KC.LQT.P (allN)

@[expose] noncomputable def trV (g : Nat → Nat → Nat) (P Lb : Nat → Nat) (f : Nat) :
    Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ x => x)
    (fun _ ih i x => nIf(Nat.beq i 0, x, g (Lb i) (ih (P i) x))) f

@[expose] noncomputable def trQ (q : Nat → Nat) (P Lb : Nat → Nat) (f : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun _ ih i => nIf(Nat.beq i 0, 0, Nat.mod (Nat.add (q (Lb i)) (ih (P i))) 2)) f

@[expose] noncomputable def treeAtK (ng : Nat) (P Lb : Nat → Nat) (i : Nat) : Bool :=
  bAnd(Nat.blt (P i) i, Nat.blt (Lb i) ng)

@[expose] noncomputable def edgeAtK (g : Nat → Nat → Nat) (q : Nat → Nat) (P Lb : Nat → Nat)
    (E : Nat → Nat → Nat) (f N ng : Nat) (bs : List Nat) (i : Nat) : Bool :=
  allN ng fun k => bAnd(Nat.blt (E i k) N,
    bAnd(eqOnL bs (trV g P Lb f (E i k)) (fun b => g k (trV g P Lb f i b)),
      Nat.beq (trQ q P Lb f (E i k)) (Nat.mod (Nat.add (q k) (trQ q P Lb f i)) 2)))

@[expose] noncomputable def keyV (n : Nat) (ps : List Nat) (h : Nat → Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun p _ acc => Nat.add (h p) (Nat.mul n acc)) ps

@[expose] noncomputable def sortAtK (key SK SKI : Nat → Nat) (N j : Nat) : Bool :=
  bAnd(Nat.blt (SKI j) N, bAnd(Nat.beq (SK (SKI j)) j,
    bIf(Nat.blt (Nat.succ j) N, Nat.blt (key (SK j)) (key (SK (Nat.succ j))), true)))

end CFSG.KC.HeLoc

end
