module

public import Certificates.Data.Kernel.GammaUOrbK

public section

namespace CFSG.KC.GUF

open CFSG.KC.IF4C CFSG.KC.GUV CFSG.KC.GUO

@[expose] noncomputable def rdBit (B v b : Nat) : Nat := bif Nat.beq (ap12 B v) v then 0 else b

@[expose] noncomputable def rd (B : Nat) : Nat :=
  Nat.add (rdBit B 971 1) (Nat.add (rdBit B 973 2) (Nat.add (rdBit B 974 4)
    (Nat.add (rdBit B 15 8) (rdBit B 48 16))))

@[expose] noncomputable def outL (LT B : Nat) : Bool := !(Nat.beq B (look LT (rd B)))

@[expose] noncomputable def ltOK (TB i LT : Nat) : Bool :=
  allBelow 32 fun m =>
    Nat.beq (look LT m) (look TB (Nat.add (Nat.mul 32 i) m)) && Nat.beq (rd (look LT m)) m

@[expose] noncomputable def pcOK (TB PT : Nat) (CM : List Nat) : Bool :=
  Nat.beq (lenN CM) 64 && allBelow 64 fun e => allBelow 32 fun c =>
    Nat.beq (Nat.land (Nat.shiftRight (nthD 0 CM e) c) 1) 0 ||
      Nat.beq (look PT e) (look TB (Nat.add (Nat.mul 32 c) (Nat.mod e 32)))

@[expose] noncomputable def letD (NA NN2 h e : Nat) : Nat := bif Nat.blt e NN2 then look NA e else h

@[expose] noncomputable def letU (NA NN2 CG W Wi c e : Nat) : Nat :=
  bif Nat.blt e NN2 then look NA e
  else mulP W (mulP (look CG (Nat.add (Nat.mul 5 c) (Nat.sub e NN2))) Wi)

@[expose] noncomputable def d1At (LT u hi Lk : Nat) : Bool :=
  Nat.beq (mulP u hi) idP && Nat.beq (ap12 u 3072) 3072 && outL LT (mulP u (mulP Lk hi))

@[expose] noncomputable def d1R (NA NN2 LT PT W Wi : Nat) (hd w : List Nat) : Bool :=
  Nat.blt (nthD 0 hd 1) 64 && Nat.blt (nthD 0 hd 2) 5 && ltAll (Nat.succ NN2) w &&
    d1At LT (wordF (letD NA NN2 (mulP W (mulP (look PT (nthD 0 hd 1)) Wi))) w) (nthD 0 hd 3)
      (look LT (Nat.shiftLeft 1 (nthD 0 hd 2)))

@[expose] noncomputable def eqAt (TB LT W Wi c m : Nat) : Bool :=
  !(outL LT (mulP W (mulP (look TB (Nat.add (Nat.mul 32 c) m)) Wi))) &&
    Nat.beq (mulP Wi (mulP (look LT m) W))
      (look TB (Nat.add (Nat.mul 32 c) (rd (mulP Wi (mulP (look LT m) W)))))

@[expose] noncomputable def eqR (TB LT W Wi : Nat) (hd : List Nat) : Bool :=
  Nat.blt (nthD 0 hd 1) 32 && Nat.beq (ap12 W 3072) 3072 &&
    allBelow 32 (eqAt TB LT W Wi (nthD 0 hd 1))

@[expose] noncomputable def f4I (TH x y : Nat) : Bool :=
  !(Nat.beq x 0) && !(Nat.beq y 0) && !(Nat.beq y x) && !(Nat.beq y (ap12 TH x)) &&
    !(Nat.beq y (Nat.xor x (ap12 TH x)))

@[expose] noncomputable def notH (LT A : Nat) (HM : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun h _ ih => !(Nat.beq A (look LT h)) && ih) HM

@[expose] noncomputable def d2uAt (TH LT : Nat) (HM : List Nat) (m₁ m₂ A u₁ u₂ : Nat) : Bool :=
  unitP TH A && !(Nat.beq A idP) && notH LT A HM && Nat.blt m₁ 32 && Nat.blt m₂ 32 &&
    Nat.beq (mulP A u₁) (mulP u₁ (look LT m₁)) && Nat.beq (mulP A u₂) (mulP u₂ (look LT m₂)) &&
    f4I TH (ap12 u₁ 3072) (ap12 u₂ 3072)

@[expose] noncomputable def d2uR (TH NA NN2 : Nat) (HM : List Nat) (CG LT W Wi : Nat)
    (rec : List (List Nat)) : Bool :=
  Nat.blt (nthD 0 (nthD [] rec 0) 1) 32 && Nat.blt (nthD 0 (nthD [] rec 0) 2) 32 &&
    ltAll (Nat.add NN2 5) (nthD [] rec 1) && ltAll (Nat.add NN2 5) (nthD [] rec 2) &&
    d2uAt TH LT HM (nthD 0 (nthD [] rec 0) 3) (nthD 0 (nthD [] rec 0) 4)
      (look LT (nthD 0 (nthD [] rec 0) 2))
      (wordF (letU NA NN2 CG W Wi (nthD 0 (nthD [] rec 0) 1)) (nthD [] rec 1))
      (wordF (letU NA NN2 CG W Wi (nthD 0 (nthD [] rec 0) 1)) (nthD [] rec 2))

@[expose] noncomputable def recOK (TH NA NN2 : Nat) (HM : List Nat) (TB CG LT PT W Wi : Nat)
    (rec : List (List Nat)) : Bool :=
  bif Nat.beq (nthD 0 (nthD [] rec 0) 0) 0 then d1R NA NN2 LT PT W Wi (nthD [] rec 0) (nthD [] rec 1)
  else bif Nat.beq (nthD 0 (nthD [] rec 0) 0) 1 then eqR TB LT W Wi (nthD [] rec 0)
  else Nat.beq (nthD 0 (nthD [] rec 0) 0) 2 && d2uR TH NA NN2 HM CG LT W Wi rec

@[expose] noncomputable def covers (CM : List Nat) (rec : List (List Nat)) (c : Nat) : Bool :=
  bif Nat.beq (nthD 0 (nthD [] rec 0) 0) 0 then
    Nat.beq (Nat.land (Nat.shiftRight (nthD 0 CM (nthD 0 (nthD [] rec 0) 1)) c) 1) 1
  else Nat.beq (nthD 0 (nthD [] rec 0) 1) c

@[expose] noncomputable def anyCov (CM : List Nat) (rs : List (List (List Nat))) (c : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun r _ ih => covers CM r c || ih) rs

@[expose] noncomputable def repAt (TH NA NN2 : Nat) (HM : List Nat) (TB CG LT PT : Nat)
    (CM : List Nat) (W Wi : Nat) (rs : List (List (List Nat))) : Bool :=
  Nat.beq (mulP W Wi) idP &&
    List.rec (motive := fun _ => Bool) true
      (fun r _ ih => recOK TH NA NN2 HM TB CG LT PT W Wi r && ih) rs &&
    allBelow 32 (anyCov CM rs)

@[expose] noncomputable def repOK (TH NA NN2 : Nat) (HM : List Nat) (TB CG LT PT : Nat)
    (CM PG : List Nat) (DT : Nat) (RP RJ : List Nat) (RW RWi : Nat)
    (SR : List (List (List (List Nat)))) (r : Nat) : Bool :=
  Nat.blt (nthD 0 RJ r) 108 && Nat.blt (nthD 0 RP r) (lenN PG) &&
    Nat.beq (look RW r) (mulP (nthD 0 PG (nthD 0 RP r)) (look DT (nthD 0 RJ r))) &&
    repAt TH NA NN2 HM TB CG LT PT CM (look RW r) (look RWi r) (nthD [] SR r)

@[expose] noncomputable def wordV (NA : Nat) (w : List Nat) (v : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun v => v) (fun e _ ih v => ap12 (look NA e) (ih v)) w v

@[expose] noncomputable def imW (NA : Nat) (w : List Nat) (R : Nat) : List Nat :=
  [wordV NA w (ap12 R 961), wordV NA w (ap12 R 48), wordV NA w (ap12 R 9), wordV NA w (ap12 R 5),
    wordV NA w (ap12 R 3), wordV NA w (ap12 R 3072)]

@[expose] noncomputable def imG (G T : Nat) : List Nat :=
  [ap12 G (ap12 T 961), ap12 G (ap12 T 48), ap12 G (ap12 T 9), ap12 G (ap12 T 5),
    ap12 G (ap12 T 3), ap12 G (ap12 T 3072)]

@[expose] noncomputable def orth (ys zs : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun y _ ih => List.rec (motive := fun _ => Bool) true
      (fun z _ ih' => Nat.beq (f0k y z) 0 && ih') zs && ih) ys

@[expose] noncomputable def cvAt (NA : Nat) (w : List Nat) (x R G T : Nat) : Bool :=
  Nat.beq (wordV NA w x) x && orth (imW NA w R) (imG G T)

@[expose] noncomputable def cvRec (NA NN2 DT : Nat) (RP : List Nat) (RW p G j : Nat)
    (rec : List Nat) : Bool :=
  Nat.blt (nthD 0 rec 0) (lenN RP) && Nat.beq (nthD 0 RP (nthD 0 rec 0)) p &&
    ltAll NN2 (dropN 1 rec) &&
    cvAt NA (dropN 1 rec) (ap12 G 3072) (look RW (nthD 0 rec 0)) G (look DT j)

@[expose] noncomputable def cvOK (NA NN2 DT : Nat) (RP : List Nat) (RW : Nat) (PG : List Nat)
    (CV : List (List (List Nat))) (p : Nat) : Bool :=
  Nat.beq (lenN (nthD [] CV p)) 108 &&
    List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
      (fun rec _ ih j => cvRec NA NN2 DT RP RW p (nthD 0 PG p) j rec && ih (Nat.succ j))
      (nthD [] CV p) 0

@[expose] noncomputable def treeN (NA NN SM : Nat) (es : List (List Nat)) (mask : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun mask => Nat.beq mask SM)
    (fun e _ ih mask =>
      Nat.blt (nthD 0 e 1) NN &&
      Nat.beq (Nat.land (Nat.shiftRight mask (nthD 0 e 2)) 1) 1 &&
      Nat.beq (ap12 (look NA (nthD 0 e 1)) (nthD 0 e 2)) (nthD 0 e 0) &&
      ih (Nat.lor mask (Nat.shiftLeft 1 (nthD 0 e 0)))) es mask

@[expose] noncomputable def ptMask (PG : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun g _ ih => Nat.lor (Nat.shiftLeft 1 (ap12 g 3072)) ih) PG

@[expose] noncomputable def treeOK (NA NN SM : Nat) (PG : List Nat) (es : List (List Nat)) : Bool :=
  treeN NA NN SM es (ptMask PG)

@[expose] noncomputable def n2OK (TH : Nat) (N2 : List Nat) (NA NN : Nat) : Bool :=
  Nat.beq (lenN N2) NN &&
    allBelow NN fun q => Nat.beq (look NA q) (nthD 0 N2 q) && guOK TH (look NA q) &&
      Nat.beq (mulP (look NA q) (look NA (Nat.add NN q))) idP

@[expose] noncomputable def pgOK (TH : Nat) (PG : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun g _ ih => guOK TH g && ih) PG

end CFSG.KC.GUF

end
