module

public import Certificates.Data.Kernel.E6TT.Enum

public section

namespace CFSG.KC.E6TT

open CFSG.KC.Enum (strictN strictB)
open Certificates.Data.E6TableT (Vec dot iform cartan)

@[expose] noncomputable def digs (w off : Nat) : Nat → Nat → List Int := fun K n =>
  Nat.rec (motive := fun _ => Nat → List Int) (fun _ => [])
    (fun _ ih K => Int.subNatNat (Nat.land K (Nat.sub (Nat.shiftLeft (nat_lit 1) w) (nat_lit 1))) off
      :: ih (Nat.shiftRight K w)) n K

@[expose] noncomputable def vecs (K r : Nat) : List Vec :=
  Nat.rec (motive := fun _ => Nat → List Vec) (fun _ => [])
    (fun _ ih K => digs (nat_lit 3) (nat_lit 3) K (nat_lit 6) :: ih (Nat.shiftRight K (nat_lit 18))) r K

@[expose] noncomputable def keyAt (TK r i : Nat) : Nat :=
  strictN (Nat.mul (nat_lit 18) r) fun w =>
    fld(TK, Nat.mul w i, Nat.sub (Nat.shiftLeft (nat_lit 1) w) (nat_lit 1))

@[expose] noncomputable def vsc (c : Int) (x y : Vec) : Vec :=
  List.zipWith (fun a b => Int.add a (Int.mul c b)) x y

@[expose] noncomputable def z6 : Vec :=
  [Int.ofNat (nat_lit 0), Int.ofNat (nat_lit 0), Int.ofNat (nat_lit 0), Int.ofNat (nat_lit 0),
    Int.ofNat (nat_lit 0), Int.ofNat (nat_lit 0)]

@[expose] noncomputable def lin (cs : List Int) : List Vec → Vec :=
  List.rec (motive := fun _ => List Vec → Vec) (fun _ => z6)
    (fun c _ ih Δ => List.rec (motive := fun _ => Vec) z6 (fun δ Δ' _ => vsc c (ih Δ') δ) Δ) cs

@[expose] noncomputable def grow (Δ : List Vec) (s : Nat) : List Int := Δ.map (iform (Δ.getD s []))

@[expose] noncomputable def rstep (X : List Vec) (gs : List Int) (s : Nat) : List Vec :=
  List.zipWith (fun g x => vsc (Int.neg g) x (X.getD s [])) gs X

@[expose] noncomputable def tabEntry (Δ : List Vec) (r TK TM n e : Nat) : Bool :=
  strictB (fld(TM, Nat.mul (nat_lit 24) e, nat_lit 16777215)) fun m =>
  bIf(Nat.beq (Nat.land m (nat_lit 31)) (nat_lit 0), vecs (keyAt TK r e) r == Δ,
    strictB (Nat.shiftRight m (nat_lit 8)) fun p =>
    strictB (Nat.land (Nat.shiftRight m (nat_lit 5)) (nat_lit 7)) fun s =>
    bAnd(Nat.blt p n, bAnd(Nat.blt s r,
      bAnd(Nat.beq (Nat.add (Nat.land fld(TM, Nat.mul (nat_lit 24) p, nat_lit 16777215) (nat_lit 31))
          (nat_lit 1)) (Nat.land m (nat_lit 31)),
        vecs (keyAt TK r e) r == rstep (vecs (keyAt TK r p) r) (grow Δ s) s))))

@[expose] noncomputable def tabOK (Δ : List Vec) (r TK TM n : Nat) : Bool :=
  CFSG.KC.Loop.allBelow n (Nat.add (Nat.shiftRight n (nat_lit 6)) (nat_lit 1)) (tabEntry Δ r TK TM n)

@[expose] noncomputable def omOK (l : List Vec) (Δ : List Vec) (r : Nat) (d : Int) (o : List Nat) :
    Bool :=
  bAnd(digs (nat_lit 8) (nat_lit 128) (o.getD 0 0) (nat_lit 6) ==
      lin (digs (nat_lit 8) (nat_lit 128) (o.getD 1 0) r) Δ,
    bAnd(digs (nat_lit 8) (nat_lit 128) (o.getD 2 0) (nat_lit 6) ==
        cartan.map (dot (digs (nat_lit 8) (nat_lit 128) (o.getD 0 0) (nat_lit 6))),
      l.all fun x =>
        Int.emod (dot x (digs (nat_lit 8) (nat_lit 128) (o.getD 2 0) (nat_lit 6))) d == 0))

@[expose] noncomputable def classK (l : List Vec) (H : List Nat) (O : List (List Nat)) : Bool :=
  bAnd((vecs (H.getD 2 0) (H.getD 0 0)).all (l.contains ·),
    bAnd(allIdx (fun i x => x ==
        lin (digs (nat_lit 3) (nat_lit 3) fld(H.getD 6 0, Nat.mul (nat_lit 16) i, nat_lit 65535)
          (H.getD 0 0)) (vecs (H.getD 2 0) (H.getD 0 0))) l 0,
      bAnd(O.all (omOK l (vecs (H.getD 2 0) (H.getD 0 0)) (H.getD 0 0) (Int.ofNat (H.getD 1 0))),
        tabOK (vecs (H.getD 2 0) (H.getD 0 0)) (H.getD 0 0) (H.getD 3 0) (H.getD 4 0) (H.getD 5 0))))

@[expose] noncomputable def wOKK (cl : List (List Vec)) :
    List (List Nat) → List (List (List Nat)) → Bool :=
  List.rec (motive := fun _ => List (List Nat) → List (List (List Nat)) → Bool)
    (fun Hs Os => bAnd(Nat.beq Hs.length 0, Nat.beq Os.length 0))
    (fun l _ ih Hs Os => List.rec (motive := fun _ => Bool) false
      (fun H Hs' _ => List.rec (motive := fun _ => Bool) false
        (fun O Os' _ => bAnd(classK l H O, ih Hs' Os')) Os) Hs) cl

@[expose] noncomputable def encV (x : Vec) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun a _ ih => Nat.lor (Int.toNat (Int.add a (Int.ofNat (nat_lit 3)))) (Nat.shiftLeft ih (nat_lit 3))) x

@[expose] noncomputable def encL (ys : List Vec) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun y _ ih => Nat.lor (encV y) (Nat.shiftLeft ih (nat_lit 18))) ys

@[expose] noncomputable def bsrch (TK r K n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun lo _ => lo)
    (fun _ ih lo len => strictN (Nat.shiftRight len (nat_lit 1)) fun h =>
      nIf(Nat.beq h (nat_lit 0), lo,
        nIf(Nat.ble (keyAt TK r (Nat.add lo h)) K, ih (Nat.add lo h) (Nat.sub len h), ih lo h)))
    (nat_lit 12) (nat_lit 0) n

@[expose] noncomputable def inK (H : List Nat) (f : Vec → Vec) : Bool :=
  strictB (bsrch (H.getD 3 0) (H.getD 0 0) (encL ((vecs (H.getD 2 0) (H.getD 0 0)).map f))
      (H.getD 5 0)) fun i =>
    bAnd(Nat.blt i (H.getD 5 0),
      vecs (keyAt (H.getD 3 0) (H.getD 0 0) i) (H.getD 0 0) == (vecs (H.getD 2 0) (H.getD 0 0)).map f)

@[expose] noncomputable def outK (H : List Nat) (O : List (List Nat)) (f : Vec → Vec) : Bool :=
  O.any fun o => O.any fun o' =>
    Int.emod (Int.sub (dot (f (digs (nat_lit 8) (nat_lit 128) (o.getD 0 0) (nat_lit 6)))
          (digs (nat_lit 8) (nat_lit 128) (o'.getD 2 0) (nat_lit 6)))
        (dot (digs (nat_lit 8) (nat_lit 128) (o.getD 0 0) (nat_lit 6))
          (digs (nat_lit 8) (nat_lit 128) (o'.getD 2 0) (nat_lit 6))))
      (Int.mul (Int.ofNat (H.getD 1 0)) (Int.ofNat (H.getD 1 0))) != 0

end CFSG.KC.E6TT

end
