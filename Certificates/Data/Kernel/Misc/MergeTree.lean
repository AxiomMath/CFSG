module

public import CFSG.Certificates.Kernel.Enum.Defs
public import Certificates.Data.Kernel.Spor.Chain

public section

namespace CFSG.KC.MTree

open CFSG.KC.Enum
open CFSG.KS (mask)

@[expose] noncomputable def pairEq (a c p q : Nat) : Bool :=
  bIf(bAnd(Nat.beq a p, Nat.beq c q), true, bAnd(Nat.beq a q, Nat.beq c p))

@[expose] noncomputable def edgeOK (n w : Nat) (GP I U V : Nat → Nat) (nI b x : Nat)
    (par tim dep : Nat → Nat) (root p : Nat) : Bool :=
  bIf(Nat.beq p root, Nat.beq (dep p) (nat_lit 0),
    strictB (par p) fun q => strictB (tim p) fun t =>
      bAnd(Nat.blt q n, bAnd(Nat.beq (dep p) (Nat.succ (dep q)),
        bIf(Nat.beq t (nat_lit 0), pairEq p q b x,
          bAnd(Nat.ble t nI, strictB (Nat.sub t (nat_lit 1)) fun k => strictB (I k) fun i =>
            pairEq p q (pg w (mask w) (GP i) (U k)) (pg w (mask w) (GP i) (V k)))))))

@[expose] noncomputable def topK (par tim : Nat → Nat) (root k fuel p : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun p => p)
    (fun _ ih p => nIf(bIf(Nat.beq p root, true, Nat.blt k (tim p)), p, strictN (par p) ih)) fuel p

@[expose] noncomputable def mtOK (n w : Nat) (GP I U V : Nat → Nat) (nI b x : Nat)
    (par tim dep : Nat → Nat) (root : Nat) : Bool :=
  bAnd(Nat.blt root n, bAnd(allN n (edgeOK n w GP I U V nI b x par tim dep root),
    allN nI fun k => Nat.beq (topK par tim root k n (U k)) (topK par tim root k n (V k))))

end CFSG.KC.MTree

end
