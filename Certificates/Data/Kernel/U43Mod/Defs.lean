module

public import CFSG.Certificates.Kernel.Enum.Defs

public section

namespace CFSG.KC.U43Mod

open CFSG.KC.Enum

@[expose] noncomputable def lpt (G Gi : Nat → Nat → Nat) (l : Nat × Bool) (q : Nat) : Nat :=
  Prod.rec (motive := fun _ => Nat)
    (fun i s => Bool.rec (motive := fun _ => Nat) (Gi i q) (G i q) s) l

@[expose] noncomputable def wv (G Gi : Nat → Nat → Nat) (ws : List (Nat × Bool)) (q : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun q => q)
    (fun l _ ih q => strictN (ih q) (lpt G Gi l)) ws q

@[expose] noncomputable def wvI (G Gi : Nat → Nat → Nat) (ws : List (Nat × Bool)) (q : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun q => q)
    (fun l _ ih q => strictN (lpt Gi G l q) ih) ws q

@[expose] noncomputable def wSel (W : List (List (Nat × Bool))) (i : Nat) : List (Nat × Bool) :=
  List.rec (motive := fun _ => Nat → List (Nat × Bool)) (fun _ => [])
    (fun w _ ih i => Nat.rec (motive := fun _ => List (Nat × Bool)) w (fun j _ => ih j) i) W i

@[expose] noncomputable def wG (G Gi : Nat → Nat → Nat) (W : List (List (Nat × Bool)))
    (i q : Nat) : Nat :=
  wv G Gi (wSel W i) q

@[expose] noncomputable def wGi (G Gi : Nat → Nat → Nat) (W : List (List (Nat × Bool)))
    (i q : Nat) : Nat :=
  wvI G Gi (wSel W i) q

@[expose] noncomputable def baseEq (bs : List Nat) (f g : Nat → Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun p _ ih => bAnd(Nat.beq (f p) (g p), ih)) bs

@[expose] noncomputable def relsB (bs : List Nat) (G Gi : Nat → Nat → Nat)
    (rs : List (List (Nat × Bool))) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun r _ ih => bAnd(baseEq bs (wv G Gi r) (fun q => q), ih)) rs

@[expose] noncomputable def keyIs (w m : Nat) (bs : List Nat) (r : Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun p _ ih t => bAnd(Nat.beq fld(r, Nat.mul w t, m) p, ih (Nat.succ t))) bs

@[expose] noncomputable def keyMap (w m : Nat) (bs : List Nat) (f : Nat → Nat) (r r' : Nat) :
    Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun _ _ ih t => bAnd(Nat.beq fld(r', Nat.mul w t, m) (f fld(r, Nat.mul w t, m)),
      ih (Nat.succ t))) bs

@[expose] noncomputable def kClos (T : Nat → Nat) (w m iw im : Nat) (bs : List Nat) (n : Nat)
    (G : Nat → Nat → Nat) (r oc : Nat) : Nat → Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun j ih => bAnd(
    strictB fld(r, Nat.add oc (Nat.mul iw j), im) (fun c =>
      bAnd(Nat.blt c n, strictB (T c) (fun rc => keyMap w m bs (G j) r rc (nat_lit 0)))),
    ih))

@[expose] noncomputable def kRec (T : Nat → Nat) (w m iw im : Nat) (bs : List Nat) (n k : Nat)
    (G : Nat → Nat → Nat) (kb km i : Nat) : Bool :=
  strictB (T i) (fun r =>
  strictB fld(r, kb, im) (fun par =>
  strictB fld(r, Nat.add kb iw, nat_lit 15) (fun lab =>
  strictB fld(r, Nat.add kb (Nat.add iw (nat_lit 4)), nat_lit 255) (fun dep =>
  bAnd(
    bIf(Nat.beq i (nat_lit 0), true, Nat.blt (Nat.land (T (Nat.sub i (nat_lit 1))) km) (Nat.land r km)),
  bAnd(
    bIf(Nat.beq dep (nat_lit 0), keyIs w m bs r (nat_lit 0),
      bAnd(Nat.blt par n, bAnd(Nat.blt lab k, strictB (T par) (fun rp =>
        bAnd(Nat.beq fld(rp, Nat.add kb (Nat.add iw (nat_lit 4)), nat_lit 255) (Nat.sub dep (nat_lit 1)),
          keyMap w m bs (G lab) rp r (nat_lit 0)))))),
    kClos T w m iw im bs n G r (Nat.add kb (Nat.add iw (nat_lit 12))) k))))))

@[expose] noncomputable def kTree (T : Nat → Nat) (w m iw im : Nat) (bs : List Nat) (n k : Nat)
    (G : Nat → Nat → Nat) : Bool :=
  strictB (Nat.mul w (List.length bs)) (fun kb =>
    bAnd(Nat.blt (nat_lit 0) n,
      allN n (kRec T w m iw im bs n k G kb (Nat.sub (Nat.shiftLeft (nat_lit 1) kb) (nat_lit 1)))))

end CFSG.KC.U43Mod

end
