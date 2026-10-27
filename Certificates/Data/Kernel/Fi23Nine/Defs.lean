module

public import Certificates.Data.Kernel.Fi23K.Defs
public import Certificates.Data.Kernel.Spor.Row

public section

namespace CFSG.KC.Fi23Nine

open CFSG.KC.Enum CFSG.KC.Fi23K CFSG.KS.Row

@[expose] noncomputable def fD (D : Nat → Nat) (o i : Nat) : Nat :=
  rg (nat_lit 32) (nat_lit 4294967295) D o i

@[expose] noncomputable def rootOf (c : Nat) : Nat :=
  Nat.land (Nat.shiftRight c (nat_lit 21)) (nat_lit 31)

@[expose] noncomputable def ptOf (c : Nat) : Nat := Nat.land c (nat_lit 32767)

@[expose] noncomputable def nodeOf (c : Nat) : Nat :=
  Nat.land (Nat.shiftRight c (nat_lit 15)) (nat_lit 1023)

@[expose] noncomputable def forAt (H D : Nat → Nat) (q : Nat) : Bool :=
  strictB (fD D (nat_lit 0) q) fun c => strictB (rootOf c) fun i =>
    strictB (Nat.shiftRight c (nat_lit 26)) fun d =>
      bAnd(Nat.blt i (nat_lit 21), bIf(Nat.beq d (nat_lit 0), Nat.beq q (fD D (nat_lit 1051) i),
        strictB (ptOf c) fun p =>
          strictB (Nat.land (Nat.shiftRight c (nat_lit 15)) (nat_lit 63)) fun l =>
            bAnd(Nat.blt l (nat_lit 42), bAnd(Nat.blt p (nat_lit 31671),
              bAnd(Nat.beq (tb H l p) q, strictB (fD D (nat_lit 0) p) fun c' =>
                bAnd(Nat.beq (rootOf c') i,
                  Nat.beq (Nat.shiftRight c' (nat_lit 26)) (Nat.pred d)))))))

@[expose] noncomputable def forSl (H D : Nat → Nat) (lo len : Nat) : Bool :=
  allN len fun k => strictB (Nat.add lo k) fun q =>
    bIf(Nat.blt q (nat_lit 31671), forAt H D q, true)

@[expose] noncomputable def lgK (D : Nat → Nat) : Bool :=
  allN (nat_lit 144) fun k => strictB (fD D (nat_lit 990) k) fun p =>
    bAnd(Nat.blt p (nat_lit 31671),
      bAnd(Nat.beq (rootOf (fD D (nat_lit 0) p)) (Nat.add (nat_lit 3) (Nat.shiftRight k (nat_lit 3))),
        bIf(Nat.beq (Nat.land k (nat_lit 7)) (nat_lit 7), true,
          Nat.blt p (fD D (nat_lit 990) (Nat.succ k)))))

@[expose] noncomputable def trAt (A : Nat → Nat → Nat) (ok : Nat → Bool) (D : Nat → Nat)
    (o r k : Nat) : Bool :=
  strictB (fD D o k) fun c => strictB (ptOf c) fun p =>
    bAnd(Nat.blt p (nat_lit 31671), bIf(Nat.beq k (nat_lit 0), Nat.beq p r,
      strictB (nodeOf c) fun pa => strictB (Nat.shiftRight c (nat_lit 25)) fun z =>
        bAnd(Nat.blt pa k, bAnd(ok z, Nat.beq (A z (ptOf (fD D o pa))) p))))

@[expose] noncomputable def trK (A : Nat → Nat → Nat) (ok : Nat → Bool) (D : Nat → Nat)
    (o r n : Nat) : Bool :=
  allN n (trAt A ok D o r)

@[expose] noncomputable def srtAt (D : Nat → Nat) (o s n j : Nat) : Bool :=
  strictB (fD D s j) fun c => strictB (nodeOf c) fun m =>
    bAnd(Nat.blt m n, bAnd(Nat.beq (ptOf (fD D o m)) (ptOf c),
      bIf(Nat.blt (Nat.succ j) n, Nat.blt (ptOf c) (ptOf (fD D s (Nat.succ j))), true)))

@[expose] noncomputable def srtK (D : Nat → Nat) (o s n : Nat) : Bool :=
  allN n (srtAt D o s n)

@[expose] noncomputable def memL (p : Nat) (s : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun a _ ih => bIf(Nat.beq p a, true, ih)) s

@[expose] noncomputable def ltL (b : Nat) (s : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun a _ ih => bAnd(Nat.blt a b, ih)) s

@[expose] noncomputable def mapsL (f : Nat → Nat) (s : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun a _ ih => bAnd(memL (f a) s, ih)) s

@[expose] noncomputable def clK (H : Nat → Nat) (s : List Nat) : Bool :=
  allN (nat_lit 42) fun l => mapsL (tb H l) s

@[expose] noncomputable def cK (G D : Nat → Nat) (cw sp : List Nat) : Bool :=
  (List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun a _ ih j => bAnd(Nat.beq (wv G cw a) (fD D (nat_lit 1051) j), ih (Nat.succ j))) sp)
    (nat_lit 21)

@[expose] noncomputable def wf (G : Nat → Nat) (w : List Nat) (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun x => x)
    (fun r _ ih x => strictN (tb G r x) ih) w x

@[expose] noncomputable def itW (G : Nat → Nat) (w : List Nat) (e x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun x => x)
    (fun _ ih x => strictN (wf G w x) ih) e x

@[expose] noncomputable def xyK (G : Nat → Nat) (xw yw s2 s4 : List Nat) : Bool :=
  bAnd(allN (nat_lit 6) fun b => bAnd(Nat.beq (itW G xw (nat_lit 6) b) b,
      bAnd(Nat.beq (itW G yw (nat_lit 12) b) b,
        Nat.beq (itW G xw (nat_lit 2) (itW G yw (nat_lit 4) b))
          (itW G yw (nat_lit 4) (itW G xw (nat_lit 2) b)))),
  bAnd(Nat.beq (itW G xw (nat_lit 2) (nat_lit 0)) (nat_lit 0),
  bAnd(Nat.beq (itW G yw (nat_lit 4) (nat_lit 0)) (nat_lit 0),
  bAnd(mapsL (itW G xw (nat_lit 2)) s2, bAnd(mapsL (itW G yw (nat_lit 4)) s2,
  bAnd(mapsL (itW G xw (nat_lit 2)) s4, bAnd(mapsL (itW G yw (nat_lit 4)) s4,
    strictB (itW G xw (nat_lit 2) (nat_lit 2)) fun a => strictB (itW G yw (nat_lit 4) (nat_lit 2))
      fun b => bAnd(Bool.not (Nat.beq a (nat_lit 2)), bAnd(Bool.not (Nat.beq b (nat_lit 2)),
        bAnd(Bool.not (Nat.beq b a), Bool.not (Nat.beq b (itW G xw (nat_lit 2) a))))))))))))

end CFSG.KC.Fi23Nine

end
