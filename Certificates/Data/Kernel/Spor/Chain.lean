module

public import CFSG.Certificates.Kernel.Enum.Defs

public section

namespace CFSG.KS

open CFSG.KC.Enum

@[expose] noncomputable def mask (w : Nat) : Nat :=
  Nat.sub (Nat.shiftLeft (nat_lit 1) w) (nat_lit 1)

@[expose] noncomputable def blk (T b pm j : Nat) : Nat := fld(T, Nat.mul b j, pm)

@[expose] noncomputable def hasBit (M l : Nat) : Bool :=
  Nat.blt (nat_lit 0) (Nat.land M (Nat.shiftLeft (nat_lit 1) l))

@[expose] noncomputable def foldUp (n : Nat) (f : Nat → Nat → Nat) (s : Nat) : Nat :=
  foldN n (fun i s => f (Nat.sub (Nat.sub n (nat_lit 1)) i) s) s

@[expose] noncomputable def pinvS (n w m p : Nat) : Nat :=
  foldN n (fun i s => Nat.lor s (Nat.shiftLeft i (Nat.mul w (pg w m p i)))) (nat_lit 0)

@[expose] noncomputable def ppow (n w m idn p k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) idn (fun _ ih => strictN ih (fun q => pcomp n w m p q)) k

@[expose] noncomputable def lcnt (S : Nat) : Nat := Nat.land S (nat_lit 65535)

@[expose] noncomputable def lpt (w m S k : Nat) : Nat :=
  fld(S, Nat.add (nat_lit 16) (Nat.mul w k), m)

@[expose] noncomputable def lpos (w m nw S x : Nat) : Nat :=
  fld(S, Nat.add (Nat.add (nat_lit 16) nw) (Nat.mul w x), m)

@[expose] noncomputable def ltr (nw pm S k : Nat) : Nat :=
  fld(S, Nat.add (Nat.add (nat_lit 16) (Nat.add nw nw)) (Nat.mul nw k), pm)

@[expose] noncomputable def ltri (n nw pm S k : Nat) : Nat :=
  fld(S, Nat.add (Nat.add (nat_lit 16) (Nat.add nw nw)) (Nat.mul nw (Nat.add n k)), pm)

@[expose] noncomputable def lvOff (n nw : Nat) : Nat :=
  Nat.add (Nat.add (nat_lit 16) (Nat.add nw nw)) (Nat.mul nw (Nat.add n n))

@[expose] noncomputable def llv (n nw S : Nat) : Nat := Nat.shiftRight S (lvOff n nw)

@[expose] noncomputable def lInit (n w m nw pm idn r LV : Nat) : Nat :=
  Nat.lor (Nat.lor (Nat.lor (nat_lit 1) (Nat.shiftLeft r (nat_lit 16)))
      (Nat.sub (Nat.shiftLeft pm (Nat.add (nat_lit 16) nw))
        (Nat.shiftLeft m (Nat.add (Nat.add (nat_lit 16) nw) (Nat.mul w r)))))
    (Nat.lor (Nat.lor (Nat.shiftLeft idn (Nat.add (nat_lit 16) (Nat.add nw nw)))
        (Nat.shiftLeft idn (Nat.add (Nat.add (nat_lit 16) (Nat.add nw nw)) (Nat.mul nw n))))
      (Nat.shiftLeft LV (lvOff n nw)))

@[expose] noncomputable def lAdd (n w m nw S q t ti : Nat) : Nat :=
  strictN (lcnt S) (fun c =>
    Nat.add (Nat.sub (Nat.add (Nat.add S (nat_lit 1)) (Nat.shiftLeft q (Nat.add (nat_lit 16) (Nat.mul w c))))
        (Nat.shiftLeft (Nat.sub m c) (Nat.add (Nat.add (nat_lit 16) nw) (Nat.mul w q))))
      (Nat.add (Nat.shiftLeft t (Nat.add (Nat.add (nat_lit 16) (Nat.add nw nw)) (Nat.mul nw c)))
        (Nat.shiftLeft ti (Nat.add (Nat.add (nat_lit 16) (Nat.add nw nw)) (Nat.mul nw (Nat.add n c))))))

@[expose] noncomputable def bfsLetter (n w m nw pm LT p tp l S : Nat) : Nat :=
  strictN (blk LT nw pm l) (fun L =>
  strictN (pg w m L p) (fun q =>
  nIf(Nat.beq (lpos w m nw S q) m,
    strictN (pcomp n w m L tp) (fun t => strictN (pinvS n w m t) (fun ti => lAdd n w m nw S q t ti)),
    S)))

@[expose] noncomputable def bfsStep (n w m nw pm LT NL LV h S : Nat) : Nat :=
  nIf(Nat.blt h (lcnt S),
    strictN (lpt w m S h) (fun p => strictN (ltr nw pm S h) (fun tp =>
      foldUp NL (fun l S => nIf(hasBit LV l, bfsLetter n w m nw pm LT p tp l S, S)) S)),
    S)

@[expose] noncomputable def bfs (n w m nw pm idn LT NL LV r : Nat) : Nat :=
  foldUp n (bfsStep n w m nw pm LT NL LV) (lInit n w m nw pm idn r LV)

@[expose] noncomputable def fixMask (w m nw pm LT NL LV b : Nat) : Nat :=
  foldUp NL (fun l M => nIf(bAnd(hasBit LV l, Nat.beq (pg w m (blk LT nw pm l) b) b),
    Nat.lor M (Nat.shiftLeft (nat_lit 1) l), M)) (nat_lit 0)

@[expose] noncomputable def levels (n w m nw pm idn LT NL : Nat) (bs : List Nat) :
    Nat → (List Nat → Nat → Bool) → Bool :=
  List.rec (motive := fun _ => Nat → (List Nat → Nat → Bool) → Bool)
    (fun LV k => k [] LV)
    (fun b _ ih LV k =>
      strictB (bfs n w m nw pm idn LT NL LV b) (fun S =>
      strictB (fixMask w m nw pm LT NL LV b) (fun LV' =>
        ih LV' (fun Ls LVt => k (List.cons S Ls) LVt))))
    bs

@[expose] noncomputable def sift (n w m nw pm idn : Nat) (Ls : List Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool)
    (fun g => Nat.beq g idn)
    (fun S _ ih g =>
      strictB (lpos w m nw S (pg w m g (lpt w m S (nat_lit 0)))) (fun k =>
      bIf(Nat.blt k (lcnt S),
        strictB (pcomp n w m (ltri n nw pm S k) g) ih,
        false)))
    Ls

@[expose] noncomputable def schreierOK (n w m nw pm idn LT NL S : Nat) (rest : List Nat) : Bool :=
  strictB (llv n nw S) (fun LV =>
  allN NL (fun l => bIf(hasBit LV l,
    strictB (blk LT nw pm l) (fun L =>
    allN (lcnt S) (fun k =>
      strictB (lpos w m nw S (pg w m L (lpt w m S k))) (fun ky =>
      bIf(Nat.blt ky (lcnt S),
        strictB (pcomp n w m (ltri n nw pm S ky) (pcomp n w m L (ltr nw pm S k)))
          (sift n w m nw pm idn rest),
        false)))),
    true)))

@[expose] noncomputable def chainSch (n w m nw pm idn LT NL : Nat) (Ls : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun S rest ih => bAnd(schreierOK n w m nw pm idn LT NL S rest, ih)) Ls

@[expose] noncomputable def maskId (nw pm idn LT NL LV : Nat) : Bool :=
  allN NL (fun l => bIf(hasBit LV l, Nat.beq (blk LT nw pm l) idn, true))

@[expose] noncomputable def sizesEq (Ls : List Nat) : List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool)
    (fun L => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) L)
    (fun S _ ih L => List.rec (motive := fun _ => Bool) false
      (fun x xs _ => bAnd(Nat.beq (lcnt S) x, ih xs)) L)
    Ls

@[expose] noncomputable def lget (Ls : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun S _ ih i => Nat.rec (motive := fun _ => Nat) S (fun j _ => ih j) i) Ls

end CFSG.KS

end
