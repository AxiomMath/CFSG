module

public import Certificates.Data.Kernel.BfsPinKeyRun

public section

namespace CFSG.KC.BfsPin

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw
open CFSG.KLie.CT (fget)

@[expose] noncomputable def seedPt (n w N : Nat) (G T E : Nat → Nat) (i : Nat) (S : List Nat) :
    Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun s _ ih => bAnd(strictB (fget (E i) s (nat_lit 16)) fun j =>
      bAnd(Nat.blt j N, Nat.beq (pcomp n w (mask w) (G s) (T i)) (T j)), ih)) S

@[expose] noncomputable def seedMask (S : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun s _ M => Nat.lor M (Nat.shiftLeft (nat_lit 1) s)) S

@[expose] noncomputable def derivK (w : Nat) (G : Nat → Nat) (D : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun M => M)
    (fun d _ ih M => nIf(bAnd(Nat.testBit M (Nat.land d (nat_lit 127)),
        Nat.testBit M (Nat.shiftRight d (nat_lit 7))),
      ih (Nat.lor M (Nat.shiftLeft (nat_lit 1)
        (pg w (mask w) (G (Nat.land d (nat_lit 127))) (Nat.shiftRight d (nat_lit 7))))),
      nat_lit 0)) D

end CFSG.KC.BfsPin

end
