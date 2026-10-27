module

public import Certificates.Data.Kernel.XorSpan

public section

namespace CFSG.KC.SpanPin

open CFSG.KC.Enum CFSG.KC.XorSpan

@[expose] noncomputable def wf (r j : Nat) : Nat :=
  fld(r, Nat.shiftLeft j (nat_lit 4), nat_lit 65535)

@[expose] noncomputable def lexK (a b c d : Nat) : Bool :=
  bIf(Nat.blt a c, true, bAnd(Nat.beq a c, Nat.blt b d))

@[expose] noncomputable def ptK (d w m dw h hm k : Nat) (A B K W : Nat → Nat) (X : Nat → Bool)
    (o c i : Nat) : Bool :=
  strictB (K (Nat.add o i)) fun ki => strictB (W (Nat.add o i)) fun wi =>
  strictB (wf wi k) fun par => strictB (wf wi (Nat.succ k)) fun lab =>
  bAnd(rrefK d w m dw ki, bAnd(X ki,
  bAnd(allN k (fun l => strictB (wf wi l) fun q => strictB (W (Nat.add o q)) fun wq =>
    bAnd(Nat.blt q c,
    bAnd(strictB (A l) (fun a => strictB (B l) fun b =>
        mapsK d w m dw (img2 w m h hm a b) ki (K (Nat.add o q))),
      bIf(Nat.beq q (nat_lit 0), true,
        bIf(lexK i l (wf wq k) (wf wq (Nat.succ k)), false, true))))),
  bIf(Nat.beq i (nat_lit 0), bAnd(Nat.beq par (nat_lit 0), Nat.beq lab (nat_lit 0)),
    bAnd(Nat.blt par i, bAnd(Nat.blt lab k, bAnd(Nat.beq (wf (W (Nat.add o par)) lab) i,
      bIf(Nat.blt (Nat.succ i) c,
        strictB (W (Nat.add o (Nat.succ i))) (fun w2 =>
          lexK par lab (wf w2 k) (wf w2 (Nat.succ k))), true))))))))

@[expose] noncomputable def sliceK (d w m dw h hm k : Nat) (A B K W : Nat → Nat) (X : Nat → Bool)
    (o c lo len : Nat) : Bool :=
  allN len (fun t => strictB (Nat.add lo t) fun i =>
    bIf(Nat.blt i c, ptK d w m dw h hm k A B K W X o c i, true))

@[expose] noncomputable def sortK (N : Nat) (K SR : Nat → Nat) (lo len : Nat) : Bool :=
  allN len (fun t => strictB (Nat.add lo t) fun i => bIf(Nat.blt i N,
    strictB (wf (SR i) (nat_lit 0)) fun s =>
      bAnd(Nat.blt s N, bAnd(Nat.beq (wf (SR s) (nat_lit 1)) i,
        bIf(Nat.blt (Nat.succ i) N, Nat.blt (K s) (K (wf (SR (Nat.succ i)) (nat_lit 0))), true))),
    true))

end CFSG.KC.SpanPin

end
