module

public section

namespace CFSG.KC.IF4C

@[expose] noncomputable def ap12 (m x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ _ => 0)
    (fun _ ih m x => Nat.xor (bif Nat.beq (Nat.land x 1) 1 then Nat.land m 4095 else 0)
      (ih (Nat.shiftRight m 12) (Nat.shiftRight x 1))) 12 m x

@[expose] noncomputable def mulP (g h : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun _ ih h => Nat.lor (ap12 g (Nat.land h 4095)) (Nat.shiftLeft (ih (Nat.shiftRight h 12)) 12))
    12 h

@[expose] noncomputable def look (t k : Nat) : Nat :=
  Nat.land (Nat.shiftRight t (Nat.mul 144 k)) (Nat.sub (Nat.pow 2 144) 1)

@[expose] noncomputable def idP : Nat :=
  11151733894906779683522195341810241573494785

@[expose] noncomputable def fld (P c : Nat) : Nat :=
  Nat.land (Nat.shiftRight P (Nat.mul 12 c)) 4095

@[expose] noncomputable def nthD {α : Type} (d : α) (l : List α) (k : Nat) : α :=
  List.rec (motive := fun _ => Nat → α) (fun _ => d)
    (fun a _ ih k => Nat.rec (motive := fun _ => α) a (fun k' _ => ih k') k) l k

@[expose] noncomputable def dropN {α : Type} (k : Nat) (l : List α) : List α :=
  Nat.rec (motive := fun _ => List α → List α) (fun l => l)
    (fun _ ih l => List.rec (motive := fun _ => List α) [] (fun _ t _ => ih t) l) k l

@[expose] noncomputable def takeN {α : Type} (k : Nat) (l : List α) : List α :=
  Nat.rec (motive := fun _ => List α → List α) (fun _ => [])
    (fun _ ih l => List.rec (motive := fun _ => List α) [] (fun a t _ => a :: ih t) l) k l

@[expose] noncomputable def lenN {α : Type} (l : List α) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun _ _ ih => Nat.succ ih) l

@[expose] noncomputable def memN (k : Nat) (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun a _ ih => Nat.beq a k || ih) l

@[expose] noncomputable def allBelow (n : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun k ih => f k && ih) n

@[expose] noncomputable def pathP (ts as : List Nat) : Nat :=
  List.rec (motive := fun _ => List Nat → Nat) (fun _ => idP)
    (fun t _ ih as => List.rec (motive := fun _ => Nat) idP
      (fun a as' _ => mulP (look t a) (ih as')) as) ts as

@[expose] noncomputable def pathOK (os as : List Nat) : Bool :=
  List.rec (motive := fun _ => List Nat → Bool)
    (fun as => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) as)
    (fun o _ ih as => List.rec (motive := fun _ => Bool) false
      (fun a as' _ => Nat.blt a o && ih as') as) os as

section
variable (SP : Nat) (T O : List Nat) (TL : List (List Nat))

@[expose] noncomputable def recOK (i r : Nat) (rec : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false
    (fun y as _ =>
      Nat.blt y (nthD 0 O i) && pathOK (dropN (Nat.succ i) O) as &&
        Nat.beq
          (mulP (look SP (nthD 0 (nthD [] TL i) (Nat.mod r (lenN (nthD [] TL i)))))
            (look (nthD 0 T i) (Nat.div r (lenN (nthD [] TL i)))))
          (mulP (look (nthD 0 T i) y) (pathP (dropN (Nat.succ i) T) as))) rec

@[expose] noncomputable def recsOK (i : Nat) (rs : List (List Nat)) (r : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun rec _ ih r => recOK SP T O TL i r rec && ih (Nat.succ r)) rs r

@[expose] noncomputable def blkOK (R : List (List (List Nat))) (i c : Nat) : Bool :=
  recsOK SP T O TL i (takeN 32 (dropN (Nat.mul 32 c) (nthD [] R i))) (Nat.mul 32 c)

@[expose] noncomputable def cntOK (R : List (List (List Nat))) (i : Nat) : Bool :=
  Nat.beq (lenN (nthD [] R i)) (Nat.mul (nthD 0 O i) (lenN (nthD [] TL i)))

@[expose] noncomputable def treeRecs (i : Nat) (es : List (List Nat)) (x : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun e _ ih x =>
      Nat.blt (nthD 0 e 0) x && memN (nthD 0 e 1) (nthD [] TL i) &&
        Nat.beq (mulP (look SP (nthD 0 e 1)) (look (nthD 0 T i) (nthD 0 e 0)))
          (look (nthD 0 T i) x) && ih (Nat.succ x)) es x

@[expose] noncomputable def treeOK (TR : List (List (List Nat))) (i : Nat) : Bool :=
  Nat.beq (look (nthD 0 T i) 0) idP && Nat.beq (Nat.succ (lenN (nthD [] TR i))) (nthD 0 O i) &&
    treeRecs SP T TL i (nthD [] TR i) 1

end

@[expose] noncomputable def posOK (T O PS B : List Nat) (i : Nat) : Bool :=
  allBelow (nthD 0 O i) (fun x =>
    Nat.beq (fld (nthD 0 PS i) (ap12 (look (nthD 0 T i) x) (nthD 0 B i))) x)

@[expose] noncomputable def fixL (SP : Nat) (B : List Nat) (n i : Nat) : List Nat :=
  (List.range n).filter fun j => (List.range i).all fun q =>
    ap12 (look SP j) (B.getD q 0) == B.getD q 0

@[expose] noncomputable def tlOK (SP : Nat) (B : List Nat) (TL : List (List Nat)) (n i : Nat) :
    Bool :=
  TL.getD i [] == fixL SP B n i

@[expose] noncomputable def invOK (SP SI n : Nat) : Bool :=
  allBelow n fun l => Nat.beq (mulP (look SP l) (look SI l)) idP

@[expose] noncomputable def wordP (SP SI : Nat) (w : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) idP
    (fun e _ ih => mulP (bif Nat.beq (Nat.mod e 2) 0 then look SP (Nat.div e 2)
      else look SI (Nat.div e 2)) ih) w

@[expose] noncomputable def wordsOK (SP SI n : Nat) (WD : List (List Nat)) (j : Nat) : Bool :=
  Nat.beq (j + lenN WD) n &&
    List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
      (fun w _ ih j => Nat.beq (look SP j) (wordP SP SI w) && w.all (fun e => Nat.blt (e / 2) j) &&
        ih (Nat.succ j)) WD j

end CFSG.KC.IF4C

end
