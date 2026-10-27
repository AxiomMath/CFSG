module

public import Certificates.Data.Kernel.GammaUNormK

public section

namespace CFSG.KC.GUO

open CFSG.KC.IF4C CFSG.KC.GUV

@[expose] noncomputable def par6 (n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun a _ => a)
    (fun _ ih a n => ih (Nat.xor a (Nat.land n 1)) (Nat.shiftRight n 1)) 6 0 n

@[expose] noncomputable def q0k (n : Nat) : Nat :=
  par6 (Nat.land (Nat.lor n (Nat.shiftRight n 6)) 63)

@[expose] noncomputable def f0k (m n : Nat) : Nat :=
  par6 (Nat.land (Nat.xor (Nat.land m (Nat.shiftRight n 6)) (Nat.land (Nat.shiftRight m 6) n)) 63)

@[expose] noncomputable def wordAp (SG : List Nat) (w : List Nat) (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun x => x)
    (fun g _ ih x => ih (ap12 (nthD 0 SG g) x)) w x

@[expose] noncomputable def xs (B : List Nat) (m : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun b _ ih m => Nat.xor (bif Nat.beq (Nat.land m 1) 1 then b else 0) (ih (Nat.shiftRight m 1)))
    B m

@[expose] noncomputable def recOK (SG : List Nat) (R : List (List Nat)) (r : List Nat) : Bool :=
  let B := nthD [] R (nthD 0 r 0)
  let c := nthD 0 r 1
  let y := nthD 0 r 2
  let D := nthD [] R (nthD 0 r 3)
  let w := dropN 10 r
  let By := B ++ [y]
  Nat.blt (nthD 0 r 3) 6 && ltAll 2 w && Nat.blt y 4096 && Nat.beq (q0k y) 0 &&
    Nat.beq (f0k y (nthD 0 B 5)) 0 &&
    allBelow 5 (fun i => Nat.beq (f0k y (nthD 0 B i)) (Nat.land (Nat.shiftRight c i) 1)) &&
    allBelow 6 (fun j =>
      let g := wordAp SG w (nthD 0 D j)
      Nat.beq g (xs By (nthD 0 r (Nat.add 4 j))) && Nat.beq (f0k g y) 0)

@[expose] noncomputable def repOK (SG : List Nat) (R : List (List Nat)) (ri : Nat)
    (rs : List (List Nat)) : Bool :=
  Nat.beq (lenN rs) 31 &&
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun r _ ih c => Nat.beq (nthD 0 r 0) ri && Nat.beq (nthD 0 r 1) c && recOK SG R r && ih (Nat.succ c))
    rs 1

@[expose] noncomputable def repF (R : List (List Nat)) (ri : Nat) : Bool :=
  let B := nthD [] R ri
  Nat.beq (lenN B) 6 && Nat.beq (nthD 0 B 5) 3072 &&
    allBelow 6 (fun i => Nat.blt (nthD 0 B i) 4096 && Nat.beq (q0k (nthD 0 B i)) 0) &&
    allBelow 6 (fun i => allBelow 6 fun j => Nat.beq (f0k (nthD 0 B i) (nthD 0 B j)) 0) &&
    allBelow 63 fun m => !Nat.beq (xs B (Nat.succ m)) 0

@[expose] noncomputable def treeW (GG : List Nat) (SM : Nat) (es : List (List Nat)) (mask : Nat) :
    Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun mask => Nat.beq mask SM)
    (fun e _ ih mask =>
      Nat.blt (nthD 0 e 1) 4 &&
      Nat.beq (Nat.land (Nat.shiftRight mask (nthD 0 e 2)) 1) 1 &&
      Nat.beq (ap12 (nthD 0 GG (nthD 0 e 1)) (nthD 0 e 2)) (nthD 0 e 0) &&
      ih (Nat.lor mask (Nat.shiftLeft 1 (nthD 0 e 0)))) es mask

@[expose] noncomputable def treeOK (GG : List Nat) (SM : Nat) (es : List (List Nat)) : Bool :=
  treeW GG SM es (Nat.shiftLeft 1 3072)

@[expose] noncomputable def smOK (SM : Nat) : Bool :=
  allBelow 4096 fun n =>
    Nat.beq (Nat.land (Nat.shiftRight SM n) 1) (bif Nat.beq n 0 then 0 else Nat.sub 1 (q0k n))

@[expose] noncomputable def gensOK (TH : Nat) (SG GG : List Nat) : Bool :=
  Nat.beq (lenN SG) 2 && Nat.beq (lenN GG) 4 &&
    List.rec (motive := fun _ => Bool) true
      (fun g _ ih => guOK TH g && Nat.beq (ap12 g 3072) 3072 && ih) SG &&
    List.rec (motive := fun _ => Bool) true (fun g _ ih => guOK TH g && ih) GG

end CFSG.KC.GUO

end
