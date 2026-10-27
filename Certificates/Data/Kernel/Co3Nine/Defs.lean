module

public import Certificates.Data.Kernel.Spor.Chain

public section

namespace CFSG.KS.Co3Nine

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def imK (P p : Nat) : Nat := pg (nat_lit 9) (mask (nat_lit 9)) P p

@[expose] noncomputable def ltK (S SI : Nat → Nat) (l : Nat) : Nat :=
  nIf(Nat.blt l (nat_lit 8), S (Nat.sub l (nat_lit 1)), SI (Nat.sub l (nat_lit 8)))

@[expose] noncomputable def walkK (S SI : Nat → Nat) (wd : List Nat) (p : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) p
    (fun l _ ih => strictN ih (fun q => imK (ltK S SI l) q)) wd

@[expose] noncomputable def keyK (f : Nat → Nat) (L : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun p _ ih => Nat.lor (Nat.shiftLeft (nat_lit 1) (f p)) ih) L

@[expose] noncomputable def lettersK (wd : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun l _ ih => bAnd(Nat.blt (nat_lit 0) l, bAnd(Nat.blt l (nat_lit 15), ih))) wd

@[expose] noncomputable def ptsK (L : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun p _ ih => bAnd(Nat.blt p (nat_lit 276), ih)) L

@[expose] noncomputable def eqPtK (f g : Nat → Nat) : Bool :=
  allN (nat_lit 276) (fun p => Nat.beq (f p) (g p))

@[expose] noncomputable def xyK (S SI : Nat → Nat) (Y : List Nat) (kY : Nat) (wx wy : List Nat) :
    Bool :=
  bAnd(lettersK wx, bAnd(lettersK wy,
  bAnd(eqPtK (fun p => walkK S SI wx (walkK S SI wx (walkK S SI wx p))) (fun p => p),
  bAnd(eqPtK (fun p => walkK S SI wy (walkK S SI wy (walkK S SI wy p))) (fun p => p),
  bAnd(eqPtK (fun p => walkK S SI wx (walkK S SI wy p)) (fun p => walkK S SI wy (walkK S SI wx p)),
  bAnd(bIf(eqPtK (walkK S SI wx) (fun p => p), false, true),
  bAnd(bIf(eqPtK (walkK S SI wy) (fun p => p), false, true),
  bAnd(bIf(eqPtK (walkK S SI wy) (walkK S SI wx), false, true),
  bAnd(bIf(eqPtK (walkK S SI wy) (fun p => walkK S SI wx (walkK S SI wx p)), false, true),
  bAnd(Nat.beq (keyK (walkK S SI wx) Y) kY, Nat.beq (keyK (walkK S SI wy) Y) kY))))))))))

@[expose] noncomputable def tFixK (TS : Nat → Nat) (Y : List Nat) (kY : Nat) : Bool :=
  allN (nat_lit 8) (fun t => Nat.beq (keyK (fun p => imK (TS t) p) Y) kY)

@[expose] noncomputable def rowK (S SI TS : Nat → Nat) (Y : List Nat) (kY k t : Nat)
    (w : List Nat) : Bool :=
  bAnd(lettersK w, bAnd(Nat.beq (keyK (walkK S SI w) Y) k,
    bIf(Nat.beq k kY, true, bAnd(Nat.blt t (nat_lit 8),
      bIf(Nat.beq (keyK (fun p => imK (TS t) (walkK S SI w p)) Y) k, false, true)))))

@[expose] noncomputable def rowsK (S SI TS : Nat → Nat) (Y : List Nat) (kY : Nat) :
    List Nat → List (List Nat) → Bool :=
  List.rec (motive := fun _ => List (List Nat) → Bool)
    (fun es => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) es)
    (fun k _ ih es => List.rec (motive := fun _ => Bool) false
      (fun e es' _ => List.rec (motive := fun _ => Bool) false
        (fun t w _ => bAnd(rowK S SI TS Y kY k t w, ih es')) e) es)

@[expose] noncomputable def cntK (L : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ _ ih => Nat.succ ih) L

@[expose] noncomputable def sortedK (L : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun x xs ih => bAnd(List.rec (motive := fun _ => Bool) true (fun y _ _ => Nat.blt x y) xs, ih))
    L

@[expose] noncomputable def co39K (S SI TS : Nat → Nat) (Y wx wy ks : List Nat)
    (es : List (List Nat)) : Bool :=
  strictB (keyK (fun p => p) Y) (fun kY =>
    bAnd(ptsK Y, bAnd(xyK S SI Y kY wx wy, bAnd(tFixK TS Y kY,
    bAnd(Nat.beq (cntK ks) (nat_lit 315), bAnd(sortedK ks, rowsK S SI TS Y kY ks es))))))

end CFSG.KS.Co3Nine

end
