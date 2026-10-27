module

public import Certificates.Data.Kernel.Spor.PNode

public section

namespace CFSG.KS.PNode4

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum CFSG.KS.PNode

@[expose] noncomputable def node4K (n w m N : Nat) (T PL : Nat → Nat) (PP SQ : List Nat)
    (i nw : Nat) : Bool :=
  bIf(Nat.beq (parK PP (pathK PL i i)) (nat_lit 1), true,
    strictB (T i) (fun t => strictB (Nat.shiftRight nw (nat_lit 1)) (fun h =>
      bIf(Nat.beq (Nat.land nw (nat_lit 1)) (nat_lit 1),
        bAnd(Nat.blt h n,
          bIf(Nat.beq (pg w m t (pg w m t (pg w m t (pg w m t h)))) h, false, true)),
        strictB (Nat.sub h (nat_lit 1)) (fun j =>
          bAnd(Nat.blt j N, bAnd(bIf(Nat.beq j (nat_lit 0), true, memK j SQ),
            Nat.beq (pcomp n w m t t) (T j))))))))

@[expose] noncomputable def nodes4K (n w m N : Nat) (T PL : Nat → Nat) (PP SQ : List Nat)
    (NW : List Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun nw _ ih i => bAnd(node4K n w m N T PL PP SQ i nw, ih (Nat.succ i))) NW

end CFSG.KS.PNode4

end
