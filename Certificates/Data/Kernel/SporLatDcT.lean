module

public import Certificates.Data.Kernel.SporLatDcP

public section

namespace CFSG.KC.SLDc

open CFSG.KC.E64F CFSG.QuasithinUnique.Ch1.SporLat

@[expose] noncomputable def allRc {α : Type} (p : α → Bool) (xs : List α) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun a _ ih => p a && ih) xs

@[expose] noncomputable def zipAllRc {α β : Type} (f : α → β → Bool) (xs : List α) :
    List β → Bool :=
  List.rec (motive := fun _ => List β → Bool) (fun _ => true)
    (fun a _ ih ys => List.rec (motive := fun _ => Bool) true (fun b ys' _ => f a b && ih ys') ys)
    xs

@[expose] noncomputable def mapRc {α β : Type} (f : α → β) (xs : List α) : List β :=
  List.rec (motive := fun _ => List β) [] (fun a _ ih => f a :: ih) xs

@[expose] noncomputable def insORc (a : Nat) (xs : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) [a]
    (fun b l ih => bif Nat.ble a b then a :: b :: l else b :: ih) xs

@[expose] noncomputable def insNRc (xs : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) [] (fun a _ ih => insORc a ih) xs

@[expose] noncomputable def encRc (n : Nat) (xs : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0
    (fun p _ acc => Nat.add (Nat.add p 1) (Nat.mul (Nat.add n 1) acc)) xs

@[expose] noncomputable def incFRc (a : Nat) (xs : List Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun b _ ih p => Nat.blt p b && ih b) xs a

@[expose] noncomputable def incRc (xs : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun a l _ => incFRc a l) xs

@[expose] noncomputable def allIdxRc {α : Type} (f : Nat → α → Bool) (c : Nat) (xs : List α) :
    Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun a _ ih k => f k a && ih (Nat.succ k)) xs c

@[expose] noncomputable def eqLRc (xs : List Nat) : List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool)
    (fun ys => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) ys)
    (fun a _ ih ys => List.rec (motive := fun _ => Bool) false
      (fun b ys' _ => Nat.beq a b && ih ys') ys) xs

@[expose] noncomputable def imgRc (M w K p : Nat) (y : List Nat) : Bool :=
  allRc (fun q => Nat.blt q M) y && Nat.beq (slotDc w K p) (encRc M y)

@[expose] noncomputable def tabTD (n w : Nat) (ts : Array (Array Nat)) (pts : List (List Nat))
    (P : Nat) : List (List Nat) → Bool :=
  allIdxRc (fun l row => Nat.beq row.length pts.length &&
    zipAllRc (fun a x => Nat.blt a pts.length &&
      Nat.beq (encRc n (insNRc (mapRc (fun p => (ts.getD l #[]).toList.getD p 0) x)))
        (slotDc w P a)) row pts) 0

@[expose] noncomputable def omPKo (actF : Nat → List Nat → List Nat) (x0 : List Nat)
    (nl M w n : Nat) (lbl rows : List (List Nat)) (par via : List Nat) (K : Nat)
    (R ord : List Nat) : Bool :=
  (lbl.headD [] == x0) && Nat.blt 0 n && Nat.beq lbl.length n && Nat.blt n (Nat.pow 2 w) &&
    allRc (fun x => allRc (fun q => Nat.blt q M) x && Nat.blt (encRc M x) (Nat.pow 2 w)) lbl &&
    (List.range nl).all (fun l => Nat.beq (rows.getD l []).length n &&
      zipAllRc (fun a x => Nat.blt a n && imgRc M w K a (actF l x)) (rows.getD l []) lbl) &&
    Nat.beq par.length n && Nat.beq via.length n &&
    allIdxRc (fun i e => Nat.beq i 0 ||
      (Nat.blt e.1 i && Nat.blt e.2 nl && Nat.beq (slotDc w (R.getD e.2 0) e.1) i)) 0
      (List.zip par via) &&
    Nat.beq ord.length n && allRc (fun i => Nat.blt i n) ord && incRc (mapRc (slotDc w K) ord)

@[expose] noncomputable def omTK (n w wi : Nat) (ts : Array (Array Nat)) (x0 : List Nat)
    (pts ci li : List (List Nat)) (ord : List Nat) (lbl rows : List (List Nat))
    (par via : List Nat) (P : Nat) (CI : List Nat) : Bool :=
  allRc (fun p => allRc (fun q => Nat.blt q n) p) pts && incRc (mapRc (encRc n) pts) &&
    allRc (fun c => Nat.blt c (Nat.pow 2 w)) (mapRc (encRc n) pts) &&
    Nat.ble pts.length (Nat.pow 2 wi) && Nat.beq ci.length ts.size && tabTD n w ts pts P ci &&
    (lbl.headD [] == x0) && Nat.beq li.length lbl.length &&
    zipAllRc (fun a b => allRc (fun q => Nat.blt q pts.length) a &&
      eqLRc (mapRc (slotDc w P) a) b) li lbl &&
    omPKo (fun l x => insNRc (mapRc (slotDc wi (CI.getD l 0)) x)) (li.headD []) ts.size
      pts.length 64 li.length li rows par via (packDc 64 (li.map (encodeSet pts.length)))
      (rows.map (packDc 64)) ord

@[expose] noncomputable def omOKT (n w wi : Nat) (ts : Array (Array Nat)) (x0 : List Nat)
    (pts ci li : List (List Nat)) (ord : List Nat) (O : OmegaData (List Nat)) : Bool :=
  omTK n w wi ts x0 pts ci li ord O.lbl.toList (O.pn.toList.map Array.toList) O.par.toList
    O.via.toList (packDc w (pts.map (encodeSet n))) (ci.map (packDc wi))

end CFSG.KC.SLDc

end
