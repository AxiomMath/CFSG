module

public import Certificates.Data.Kernel.SporSch.MathieuOC
public import Certificates.Data.Kernel.Spor.Prim
public import Certificates.Data.CFSGNative.Th.Tables

public section

namespace CFSG.KS.Sp6I

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch.MOC

@[expose] noncomputable def laneK (nw P j : Nat) : Nat :=
  Nat.land (Nat.shiftRight P (Nat.mul nw j)) (Nat.sub (Nat.shiftLeft (nat_lit 1) nw) (nat_lit 1))

@[expose] noncomputable def commPK (n w m nw P c g : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun j ih => strictB (laneK nw P j) (fun u =>
    bAnd(Nat.beq (pcomp n w m g u) (pcomp n w m u g), ih))) c

@[expose] noncomputable def memPK (nw P c g : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) false
    (fun j ih => bIf(Nat.beq (laneK nw P j) g, true, ih)) c

@[expose] noncomputable def maskPK (n w m nw idn P mk c : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) idn (fun j ih => strictN ih (fun q =>
    nIf(Nat.beq (Nat.land (Nat.shiftRight mk j) (nat_lit 1)) (nat_lit 0), q,
      pcomp n w m q (laneK nw P j)))) c

@[expose] noncomputable def spanPK (n w m nw idn P S c : Nat) : Bool :=
  allN (Nat.shiftLeft (nat_lit 1) c) (fun s => Nat.beq (laneK nw S s) (maskPK n w m nw idn P s c))

@[expose] noncomputable def conjPK (n w m nw T P y yi c : Nat) : Bool :=
  allN c (fun j => Nat.beq (laneK nw P j) (pcomp n w m (pcomp n w m yi (laneK nw T j)) y))

@[expose] noncomputable def tabPK (n w m p : Nat) (T : CFSG.Sporadic.Th.Native.Table) : Bool :=
  allN n (fun i => Nat.beq (pg w m p i) (CFSG.Sporadic.Th.Native.ap T i))

@[expose] noncomputable def tabsPK (n w m nw P : Nat) :
    List CFSG.Sporadic.Th.Native.Table → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true) (fun T _ ih j =>
    strictB (laneK nw P j) (fun p => bAnd(CFSG.KS.Prim.canonK n w m nw p,
      bAnd(tabPK n w m p T, ih (Nat.succ j)))))

@[expose] noncomputable def lenT : List CFSG.Sporadic.Th.Native.Table → Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ _ ih => Nat.succ ih)

@[expose] noncomputable def lettersNK (wd : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun l _ ih => bAnd(Nat.blt l (nat_lit 4), ih)) wd

@[expose] noncomputable def wordNK (n w m idn : Nat) (S SI : Nat → Nat) (wd : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) idn (fun l _ ih => strictN ih (fun q =>
    pcomp n w m (nIf(Nat.blt l (nat_lit 2), S l, SI (Nat.sub l (nat_lit 2)))) q)) wd

@[expose] noncomputable def centCntK (n w m nw : Nat) (LR TR : Nat → Nat) (nb idn U a S b : Nat) :
    Nat :=
  strictN U (fun U => strictN S (fun S => strictN a (fun a =>
    strictN (Nat.shiftLeft (nat_lit 1) b) (fun s =>
      enumFrom n w m nw LR TR (fun g => bAnd(commPK n w m nw U a g, bIf(memPK nw S s g, false, true)))
        nb (nat_lit 0) idn (nat_lit 0)))))

end CFSG.KS.Sp6I

end
