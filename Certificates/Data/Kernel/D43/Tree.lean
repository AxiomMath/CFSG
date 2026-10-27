module

public import Certificates.Data.Kernel.D43.Twin

public section

namespace CFSG.KC.D43

open CFSG.KC.Enum

@[expose] noncomputable def gAp (F : Nat → Nat) (d p : Nat) : Nat :=
  nIf(Nat.blt p (nat_lit 26572),
    nIf(Nat.beq d (nat_lit 0), p,
      nIf(Nat.ble d (nat_lit 8), tabAt F (Nat.sub d (nat_lit 1)) p,
        nIf(Nat.ble d (nat_lit 16),
          strictN (tabAt F (Nat.sub d (nat_lit 9)) p) fun a =>
            strictN (tabAt F (Nat.sub d (nat_lit 9)) a) fun b =>
              nIf(Nat.beq (tabAt F (Nat.sub d (nat_lit 9)) b) p, b, nat_lit 65535),
          p))),
    nat_lit 65535)

@[expose] noncomputable def wAp (F : Nat → Nat) : Nat → Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ p => p)
    (fun _ ih w p => nIf(Nat.beq w (nat_lit 0), p,
      strictN (gAp F (Nat.land w (nat_lit 31)) p) fun q => ih (Nat.shiftRight w (nat_lit 5)) q))

@[expose] noncomputable def lAp (F W : Nat → Nat) (j p : Nat) : Nat := wAp F (nat_lit 24) (W j) p

@[expose] noncomputable def bAt (B u : Nat) : Nat := fld(B, Nat.mul (nat_lit 15) u, nat_lit 32767)

@[expose] noncomputable def fixesB (F W : Nat → Nat) (B i j : Nat) : Bool :=
  allBlk (nat_lit 0) (fun u => strictB (bAt B u) fun b => Nat.beq (lAp F W j b) b) i

@[expose] noncomputable def fixChk (F W : Nat → Nat) (B i lo M j : Nat) : Bool :=
  strictB (Nat.land (Nat.shiftRight M j) (nat_lit 1)) fun m =>
    bIf(bAnd(Nat.ble lo j, fixesB F W B i j), Nat.beq m (nat_lit 1), Nat.beq m (nat_lit 0))

@[expose] noncomputable def fixAll (F W : Nat → Nat) (B i lo M : Nat) : Bool :=
  allBlk (nat_lit 0) (fixChk F W B i lo M) (nat_lit 17)

@[expose] noncomputable def recAt (R : Nat → Nat) (o t : Nat) : Nat :=
  rget R (nat_lit 4) (nat_lit 15) (nat_lit 36) (nat_lit 68719476735) (Nat.add o t)

@[expose] noncomputable def posAt (Q : Nat → Nat) (ℓ q : Nat) : Nat :=
  rget Q (nat_lit 6) (nat_lit 63) (nat_lit 16) (nat_lit 65535)
    (Nat.add (Nat.mul (nat_lit 26572) ℓ) q)

@[expose] noncomputable def ptAt (R : Nat → Nat) (o t : Nat) : Nat :=
  Nat.land (recAt R o t) (nat_lit 32767)

@[expose] noncomputable def treeChk (F W R Q : Nat → Nat) (ℓ o b M t : Nat) : Bool :=
  strictB (recAt R o t) fun e => strictB (Nat.land e (nat_lit 32767)) fun pt =>
    bAnd(Nat.blt pt (nat_lit 26572), bAnd(Nat.beq (posAt Q ℓ pt) t,
      bIf(Nat.beq t (nat_lit 0), Nat.beq pt b,
        strictB fld(e, nat_lit 15, nat_lit 32767) fun par =>
          strictB (Nat.shiftRight e (nat_lit 30)) fun lab =>
            bAnd(Nat.blt par t, bAnd(Nat.beq (Nat.land (Nat.shiftRight M lab) (nat_lit 1)) (nat_lit 1),
              Nat.beq (lAp F W lab (ptAt R o par)) pt)))))

@[expose] noncomputable def treeChunk (F W R Q : Nat → Nat) (ℓ o s b M c : Nat) : Bool :=
  allBlk (Nat.mul (nat_lit 256) c)
    (fun t => bIf(Nat.blt t s, treeChk F W R Q ℓ o b M t, true)) (nat_lit 256)

end CFSG.KC.D43

end
