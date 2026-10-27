module

public import CFSG.Certificates.Kernel.Enum.Defs
public import Certificates.Data.Kernel.Spor.Chain

public section

namespace CFSG.KC.Misc.CentPt

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def atU (n w P x : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) 0 (pg w (mask w) P x) (Nat.blt x n)

@[expose] noncomputable def commAt (n w A B p : Nat) : Bool :=
  Nat.beq (atU n w A (atU n w B p)) (atU n w B (atU n w A p))

@[expose] noncomputable def centPtK (n w N : Nat) (E : Nat → Nat) (js ps : List Nat) (z : Nat) :
    Bool :=
  allN N fun i => !(js.all fun j => ps.all fun p => commAt n w (E i) (E j) p) || Nat.beq i 0 ||
    Nat.beq i z

end CFSG.KC.Misc.CentPt

end
