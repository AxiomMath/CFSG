module

public import Certificates.Data.Kernel.Spor.BTup

public section

namespace CFSG.KS.BTup

open CFSG.KC.Enum CFSG.KS.Row

@[expose] noncomputable def btWalkF (w m : Nat) (G R : Nat → Nat) (fuel : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ p => p)
    (fun _ ih i p => strictN (btRec R i) (fun r =>
      strictN (ih (btPar r) p) (fun q => pg w m (G (btLab r)) q))) fuel

@[expose] noncomputable def btWalk (w m : Nat) (G R : Nat → Nat) (i p : Nat) : Nat :=
  btWalkF w m G R (btDep (btRec R i)) i p

@[expose] noncomputable def btPre (PRE : Nat → Nat) (d j t : Nat) : Nat :=
  rg (nat_lit 16) (nat_lit 65535) PRE (nat_lit 0) (Nat.add (Nat.mul j d) t)

@[expose] noncomputable def btPreK (n w m d mc B : Nat) (C PRE : Nat → Nat) : Bool :=
  allN mc (fun j => allN d (fun t => bAnd(Nat.blt (btPre PRE d j t) n,
    Nat.beq (pg w m (C j) (btPre PRE d j t)) (pg w m B t))))

@[expose] noncomputable def btTg (TG : Nat → Nat) (i : Nat) : Nat :=
  rg (nat_lit 64) (nat_lit 18446744073709551615) TG (nat_lit 0) i

@[expose] noncomputable def btTgIn (g : Nat) : Bool := Nat.beq (Nat.land g (nat_lit 1)) (nat_lit 1)

@[expose] noncomputable def btTgLab (g : Nat) : Nat := fld(g, nat_lit 1, nat_lit 255)

@[expose] noncomputable def btTgPar (g : Nat) : Nat := fld(g, nat_lit 9, nat_lit 4294967295)

@[expose] noncomputable def btTgDep (g : Nat) : Nat := Nat.shiftRight g (nat_lit 41)

@[expose] noncomputable def btOcK (w m d kw km mc cnt B Wr : Nat) (G K R C PRE TG : Nat → Nat)
    (i : Nat) : Bool :=
  strictB (btTg TG i) (fun g =>
  bIf(btTgIn g,
    strictB (btKey kw km K i) (fun x =>
    bIf(Nat.beq (btTgDep g) (nat_lit 0), btMov w m d Wr B x,
      strictB (btTgPar g) (fun q => strictB (btTgLab g) (fun l =>
      strictB (btTg TG q) (fun gq =>
        bAnd(Nat.blt q cnt, bAnd(Nat.blt l mc, bAnd(btTgIn gq,
        bAnd(Nat.beq (Nat.succ (btTgDep gq)) (btTgDep g),
          allN d (fun t => Nat.beq (pg w m x t)
            (pg w m (C l) (btWalk w m G R q (btPre PRE d l t))))))))))))),
    true))

@[expose] noncomputable def btOcSlK (w m d kw km mc cnt B Wr : Nat) (G K R C PRE TG : Nat → Nat)
    (lo len : Nat) : Bool :=
  allN len (fun e => strictB (Nat.add lo e) (fun i =>
    bIf(Nat.blt i cnt, btOcK w m d kw km mc cnt B Wr G K R C PRE TG i, true)))

end CFSG.KS.BTup

end
