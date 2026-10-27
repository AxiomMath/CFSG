module

public import Certificates.Data.Kernel.SporSch.PairJ3Cnt

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum

@[expose] noncomputable def mulL (ev : Nat → Nat → Nat) (bs : List Nat) (a b c : Nat) : Bool :=
  eqOnL bs (fun x => ev a (ev b x)) (ev c)

@[expose] noncomputable def lgOK (ev : Nat → Nat → Nat) (vld : Nat → Bool) (bs : List Nat)
    (L T I : Nat → Nat) (m : Nat) : Bool :=
  bAnd(allN m (fun i => vld (L i)),
  bAnd(eqOnL bs (ev (L 0)) (fun x => x),
  bAnd(allN m (fun i => allN m (fun j => strictB (T (Nat.add (Nat.mul m i) j)) (fun k =>
    bAnd(Nat.blt k m, mulL ev bs (L i) (L j) (L k))))),
  bAnd(allN m (fun i => strictB (I i) (fun k => bAnd(Nat.blt k m, mulL ev bs (L i) (L k) (L 0)))),
    allN m (fun i => allN i (fun j => bIf(eqOnL bs (ev (L i)) (ev (L j)), false, true)))))))

@[expose] noncomputable def comL (ev : Nat → Nat → Nat) (bs : List Nat) (X : Nat → Nat)
    (a : Nat) : Bool :=
  eqOnL bs (fun x => ev a (X x)) (fun x => X (ev a x))

@[expose] noncomputable def wev (ev : Nat → Nat → Nat) (G : Nat → Nat) (f w x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ x => x)
    (fun _ ih w x => Bool.rec (motive := fun _ => Nat)
      (ev (G (Nat.sub (Nat.mod w 4) 1)) (ih (Nat.div w 4) x)) x (Nat.beq w 0)) f w x

@[expose] noncomputable def wordsOK (ev : Nat → Nat → Nat) (bs : List Nat) (G L W : Nat → Nat)
    (m : Nat) : Bool :=
  allN m (fun i => eqOnL bs (ev (L i)) (wev ev G 40 (W i)))

@[expose] noncomputable def wtL (ev : Nat → Nat → Nat) (bs : List Nat) (s u v e : Nat) : Bool :=
  bAnd(eqOnL bs (fun x => ev u (ev v x)) (fun x => x),
    bIf(eqOnL bs (powF (fun x => ev s (ev u (ev s (ev v x)))) e) (fun x => x), false, true))

end CFSG.KS.SporSch

end
