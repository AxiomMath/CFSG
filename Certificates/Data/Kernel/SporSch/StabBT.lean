module

public import Certificates.Data.Kernel.SporSch.Closure

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

@[expose] noncomputable def inS (SP x : Nat) : Bool := hasBit SP x

@[expose] noncomputable def btTrAt (n nw : Nat) (TR : Nat → Nat) (R k : Nat) : Nat :=
  TR (Nat.add (roff n nw R) k)

@[expose] noncomputable def cntBT (n w : Nat) (LR TR : Nat → Nat) (SP : Nat) : Nat → Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ _ => nat_lit 1)
    (fun _ ih i h => strictN (LR i) (fun R =>
      foldN (rcnt R) (fun k acc =>
        nIf(inS SP (pg w (mask w) h (rpt w (mask w) R k)),
          Nat.add acc (strictN (nIf(Nat.beq k (nat_lit 0), h,
              pcomp n w (mask w) h (btTrAt n (Nat.mul n w) TR R k))) (fun h' =>
            strictN (Nat.succ i) (fun i' => ih i' h'))),
          acc)) (nat_lit 0)))

@[expose] noncomputable def btTop (n w : Nat) (LR TR : Nat → Nat) (SP : Nat) (KV KJ VT : Nat → Nat)
    (nL : Nat) : Nat :=
  strictN (Nat.mul n w) (fun nw => strictN (mask w) (fun m =>
  strictN (LR (nat_lit 0)) (fun R0 => strictN (LR (nat_lit 1)) (fun R1 => strictN (LR (nat_lit 2))
    (fun R2 =>
  foldN (rcnt R0) (fun k0 a0 => strictN (rpt w m R0 k0) (fun y0 =>
    nIf(inS SP y0, strictN (btTrAt n nw TR R0 k0) (fun h0 =>
      Nat.add a0 (foldN (rcnt R1) (fun k1 a1 => nIf(inS SP (pg w m h0 (rpt w m R1 k1)),
        strictN (nIf(Nat.beq k1 (nat_lit 0), h0, pcomp n w m h0 (btTrAt n nw TR R1 k1))) (fun h1 =>
        Nat.add a1 (foldN (rcnt R2) (fun k2 a2 => nIf(inS SP (pg w m h1 (rpt w m R2 k2)),
          strictN (Nat.lor (Nat.shiftLeft k0 (nat_lit 18)) (Nat.lor (Nat.shiftLeft k1 (nat_lit 9)) k2))
            (fun key => strictN (KV key) (fun j' =>
              nIf(Nat.beq j' (nat_lit 0), failC,
                strictN (Nat.sub j' (nat_lit 1)) (fun j =>
                  nIf(bAnd(Nat.blt j nL, Nat.beq (KJ j) key), Nat.add a2 (VT j), failC))))),
          a2)) (nat_lit 0))),
        a1)) (nat_lit 0))),
      a0))) (nat_lit 0))))))

@[expose] noncomputable def keyProd (n w : Nat) (LR TR : Nat → Nat) (key : Nat) : Nat :=
  strictN (Nat.mul n w) (fun nw =>
  strictN (btTrAt n nw TR (LR (nat_lit 0)) (Nat.shiftRight key (nat_lit 18))) (fun h0 =>
  strictN (pcomp n w (mask w) h0 (btTrAt n nw TR (LR (nat_lit 1))
    (Nat.land (Nat.shiftRight key (nat_lit 9)) (nat_lit 511)))) (fun h1 =>
  pcomp n w (mask w) h1 (btTrAt n nw TR (LR (nat_lit 2)) (Nat.land key (nat_lit 511))))))

@[expose] noncomputable def btLeaf (n w : Nat) (LR TR : Nat → Nat) (SP m : Nat) (KJ VT : Nat → Nat)
    (j : Nat) : Bool :=
  Nat.beq (cntBT n w LR TR SP (Nat.sub m (nat_lit 3)) (nat_lit 3) (keyProd n w LR TR (KJ j))) (VT j)

@[expose] noncomputable def btSetK (n w BP m SP : Nat) (L : List Nat) : Bool :=
  bAnd(Nat.beq (CFSG.KS.Mathieu.lenN L) m, bAnd(CFSG.KS.Mathieu.allLtN n L,
  bAnd(Nat.beq (List.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun x _ acc => Nat.lor acc (Nat.shiftLeft (nat_lit 1) x)) L) SP,
  bAnd(allN m (fun i => inS SP (pg w (mask w) BP i)),
    allN m (fun i => allN i (fun j =>
      bIf(Nat.beq (pg w (mask w) BP i) (pg w (mask w) BP j), false, true)))))))

end CFSG.KS.SporSch

end
