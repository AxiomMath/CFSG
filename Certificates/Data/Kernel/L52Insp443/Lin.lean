module

public import Certificates.Data.Kernel.Misc.GL52Mat

public section

namespace CFSG.KC.L52I

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc.GLM

@[expose] noncomputable def allK {α : Type} (p : α → Bool) (L : List α) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x _ ih => CFSG.KC.Ord.andB (p x) ih) L

@[expose] noncomputable def anyK {α : Type} (p : α → Bool) (L : List α) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun x _ ih => CFSG.KC.Ord.orB (p x) ih) L

@[expose] noncomputable def memK (x : Nat) (L : List Nat) : Bool := anyK (Nat.beq x) L

@[expose] noncomputable def nodupK (L : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x xs ih => CFSG.KC.Ord.andB (CFSG.KC.Ord.notB (memK x xs)) ih) L

@[expose] noncomputable def commK (a b : Nat) : Bool := Nat.beq (mmulK a b) (mmulK b a)

@[expose] noncomputable def mapMulK (b : Nat) (S : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) List.nil (fun s _ ih => List.cons (mmulK b s) ih) S

@[expose] noncomputable def spanK (bs : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) (List.cons idK List.nil)
    (fun b _ ih => List.append ih (mapMulK b ih)) bs

@[expose] noncomputable def diagK (us : List Nat) : List (Nat × Nat) :=
  List.rec (motive := fun _ => List (Nat × Nat)) List.nil
    (fun u _ ih => List.cons (Prod.mk u u) ih) us

@[expose] noncomputable def kerK (ps : List (Nat × Nat)) : List Nat :=
  (elimK ps (Nat.mul (nat_lit 25) (List.length ps)) (nat_lit 25)).2

@[expose] noncomputable def conjCommK (c : Nat) (ps qs : List Nat) : Bool :=
  List.rec (motive := fun _ => List Nat → Bool) (fun _ => true)
    (fun p _ ih qs => List.rec (motive := fun _ => Bool) true
      (fun q qs' _ => CFSG.KC.Ord.andB (commK c (mmulK (mmulK p c) q)) (ih qs')) qs) ps qs

@[expose] noncomputable def sRange (K zS wS ps qs : List Nat) (lo cnt : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun d acc => CFSG.KC.Ord.andB (letB (xsel K (Nat.add lo d)) fun c =>
      CFSG.KC.Ord.orB (CFSG.KC.Ord.notB (Nat.beq (rankK c) (nat_lit 5)))
        (CFSG.KC.Ord.orB (CFSG.KC.Ord.notB (conjCommK c ps qs)) (CFSG.KC.Ord.orB (memK c zS) (memK c wS)))) acc) cnt

@[expose] noncomputable def tauOK (a0 a1 wS a1S : List Nat) (τ : Nat) : Bool :=
  CFSG.KC.Ord.andB (allK (commK τ) a0) (CFSG.KC.Ord.andB (CFSG.KC.Ord.notB (memK τ wS))
    (anyK (fun a => allK (fun a' => CFSG.KC.Ord.notB (Nat.beq (mmulK τ a) (mmulK a' τ))) a1S) a1))

@[expose] noncomputable def par5 (x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun j acc => Nat.xor acc (Nat.land (Nat.shiftRight x j) (nat_lit 1))) (nat_lit 5)

@[expose] noncomputable def mvK (c v : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Nat.lor acc (Nat.shiftLeft (par5 (Nat.land (rowK c i) v)) i)) (nat_lit 5)

@[expose] noncomputable def actK (c F : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun v acc => Bool.rec (motive := fun _ => Nat) acc
      (Nat.lor acc (Nat.shiftLeft (nat_lit 1) (mvK c v))) (bitK F v)) (nat_lit 32)

@[expose] noncomputable def fixK (bs : List Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun v acc => Bool.rec (motive := fun _ => Nat) acc (Nat.lor acc (Nat.shiftLeft (nat_lit 1) v))
      (CFSG.KC.Ord.andB (CFSG.KC.Ord.notB (Nat.beq v (nat_lit 0))) (allK (fun b => Nat.beq (mvK b v) v) bs)))
    (nat_lit 32)

abbrev Rec := Nat × Nat × Nat × Nat × Nat

@[expose] noncomputable def nthR (L : List Rec) : Nat → Rec :=
  List.rec (motive := fun _ => Nat → Rec) (fun _ => (0, 0, 0, 0, 0))
    (fun x _ ih j => Nat.rec (motive := fun _ => Rec) x (fun j' _ => ih j') j) L

@[expose] noncomputable def masksR (L : List Rec) : List Nat :=
  List.rec (motive := fun _ => List Nat) List.nil (fun r _ ih => List.cons r.1 ih) L

@[expose] noncomputable def recOK (F0 m : Nat) (r : Rec) : Bool :=
  CFSG.KC.Ord.andB (Nat.beq (mmulK r.2.2.1 r.2.1) idK) (CFSG.KC.Ord.andB (Nat.beq (actK r.2.1 F0) r.1)
    (CFSG.KC.Ord.andB (Nat.blt r.2.2.2.1 m) (Nat.blt r.2.2.2.2 m)))

@[expose] noncomputable def genAt (L : List Rec) (P : Nat → Nat → Bool) (s s' : Nat) (r : Rec)
    (j : Nat) : Bool :=
  Prod.rec (motive := fun _ => Bool) (fun Fj rest => Prod.rec (motive := fun _ => Bool)
    (fun tj rest' => Prod.rec (motive := fun _ => Bool) (fun tj' _ =>
      CFSG.KC.Ord.andB (Nat.beq (actK s r.1) Fj)
        (P (mmulK (mmulK tj' s) r.2.1) (mmulK (mmulK r.2.2.1 s') tj))) rest') rest) (nthR L j)

@[expose] noncomputable def orbOK (bs : List Nat) (L : List Rec) (P : Nat → Nat → Bool)
    (sA sA' sB sB' : Nat) : Bool :=
  letB (nthR L 0).1 fun F0 =>
    CFSG.KC.Ord.andB (Nat.beq (fixK bs) F0) (CFSG.KC.Ord.andB (Nat.beq (nthR L 0).2.1 idK) (CFSG.KC.Ord.andB (nodupK (masksR L))
      (allK (fun r => CFSG.KC.Ord.andB (recOK F0 (List.length L) r)
        (CFSG.KC.Ord.andB (genAt L P sA sA' r r.2.2.2.1) (genAt L P sB sB' r r.2.2.2.2))) L)))

@[expose] noncomputable def normP (S bs : List Nat) (y y' : Nat) : Bool :=
  allK (fun b => memK (mmulK (mmulK y b) y') S) bs

@[expose] noncomputable def permP (aB aS : List (List Nat)) (y y' : Nat) : Bool :=
  allK (fun bs => anyK (fun S => normP S bs y y') aS) aB

end CFSG.KC.L52I

end
