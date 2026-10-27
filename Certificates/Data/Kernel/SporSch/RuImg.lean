module

public import Certificates.Data.Kernel.Spor.Raw

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

@[expose] noncomputable def lenNL (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ _ ih => Nat.succ ih) l

@[expose] noncomputable def memNL (x : Nat) (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun y _ ih => bIf(Nat.beq x y, true, ih)) l

@[expose] noncomputable def allGtNL (x : Nat) (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun y _ ih => bAnd(Nat.blt x y, ih)) l

@[expose] noncomputable def incNL (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x xs ih => bAnd(allGtNL x xs, ih)) l

@[expose] noncomputable def distImg (w : Nat) (G : Nat) (l : List Nat) : List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool) (fun _ => true)
    (fun p _ ih S => strictB (pg w (mask w) G p) (fun x =>
      bAnd(bIf(memNL x S, false, true), ih (x :: S)))) l

@[expose] noncomputable def sortImgK (n w G : Nat) (L M : List Nat) : Bool :=
  bAnd(Nat.beq (lenNL L) (lenNL M), bAnd(incNL M, bAnd(distImg w G L [],
    List.rec (motive := fun _ => Bool) true (fun p _ ih =>
      bAnd(Nat.blt p n, bAnd(memNL (pg w (mask w) G p) M, ih))) L)))

end CFSG.KS.SporSch

end
