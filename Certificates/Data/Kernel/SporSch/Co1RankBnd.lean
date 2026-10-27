module

public import Certificates.Data.Kernel.SporSch.Co1RankRec

public section

namespace CFSG.KC.Co1RankBnd

open CFSG.KC.Loop CFSG.KC.Co1RankCoord

@[expose] noncomputable def allLt (m : Nat) (L : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x _ ih => bAnd(Nat.blt x m, ih)) L

@[expose] noncomputable def entriesLt (m : Nat) (es : List (Nat × Nat × List Nat × List Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun e _ ih =>
    Prod.rec (motive := fun _ => Bool) (fun mode r => Prod.rec (motive := fun _ => Bool) (fun a _ =>
      bAnd(bIf(Nat.beq mode 1, Nat.blt a m, true), ih)) r) e) es

@[expose] noncomputable def bndOK (D : Co1RankCand.Dat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun p _ ih =>
    Prod.rec (motive := fun _ => Bool) (fun gs r => Prod.rec (motive := fun _ => Bool) (fun _ es =>
      bAnd(allLt (Nat.shiftLeft 1 (Nat.add D.d 7)) gs,
        bAnd(entriesLt (Nat.shiftLeft 1 D.d) es, ih))) r) p) D.reps

@[expose] noncomputable def relN (T : Co1RankTab.Dat) (m : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun k acc =>
    Nat.lor acc (Nat.shiftLeft
      (Nat.shiftRight (fld(T.REL, Nat.mul (Nat.add 7 T.d) k, mask (Nat.add 7 T.d))) 7)
      (Nat.mul T.d k))) m

@[expose] noncomputable def tabOK (T : Co1RankTab.Dat) : Bool :=
  bAnd(Nat.rec (motive := fun _ => Bool) true (fun i ih =>
      bAnd(Co1RankRec.wordOK T.nG (getL T.CW i), ih)) 128,
    strictB (Nat.mul 128 T.nG) fun m => Nat.beq (rankRC m T.d (relN T m)) T.d)

end CFSG.KC.Co1RankBnd

end
