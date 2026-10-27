module

public import Certificates.Data.Kernel.HNFFibK

public section

namespace CFSG.KC.HNFOrb

open CFSG.KC.Ord CFSG.KC.HNF26720 CFSG.KC.HNF26729 CFSG.KC.HNFFib

@[expose] def keyM : Nat := 2305843009213693951

@[expose] noncomputable def tl (l : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) [] (fun _ t _ => t) l

@[expose] noncomputable def nilB (K : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) K

@[expose] noncomputable def hdIs (k : Nat) (f : List Nat → Bool) (K : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun k' K' _ => andB (Nat.beq k k') (f K')) K

@[expose] noncomputable def emit (vec : Nat → Nat → Nat) (u x : Nat) (f : List Nat → Bool)
    (K : List Nat) : Bool :=
  strictB (Nat.mod (vec u x) keyM) fun k => hdIs k f K

@[expose] noncomputable def move (mul vec : Nat → Nat → Nat) (b ONE u : Nat)
    (L : List (Nat × Nat)) (c : Nat) (r : List Nat → List Nat → Bool) (st K : List Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool)
    (Bool.rec (motive := fun _ => Bool)
      (strictB (mul (mul (getP (ONE, ONE) L (Nat.mod c 5)).1 (getN b st 0))
          (getP (ONE, ONE) L (Nat.mod c 5)).2) fun x =>
        Bool.rec (motive := fun _ => Bool) (r (x :: st) K) (emit vec u x (r (x :: st)) K)
          (Nat.blt c 3))
      (emit vec u (getN b st 0) (r st) K) (Nat.beq c 4))
    (r (tl st) K) (Nat.beq c 3)

@[expose] noncomputable def walk (mul vec : Nat → Nat → Nat) (b ONE u : Nat)
    (L : List (Nat × Nat)) : List Nat → List Nat → List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → List Nat → Bool) (fun _ K => nilB K)
    (fun c _ ih st K => move mul vec b ONE u L c ih st K)

inductive PT where
  | lf : PT
  | nd : PT → Nat → PT → PT

@[expose] noncomputable def evO (l : List Nat) : Bool → List Nat :=
  List.rec (motive := fun _ => Bool → List Nat) (fun _ => [])
    (fun x _ ih e => Bool.rec (motive := fun _ => List Nat) (ih true) (x :: ih false) e) l

@[expose] noncomputable def ofT (n : Nat) : List Nat → PT :=
  Nat.rec (motive := fun _ => List Nat → PT) (fun _ => PT.lf)
    (fun _ ih L => List.rec (motive := fun _ => PT) PT.lf
      (fun x l _ => PT.nd (ih (evO l false)) x (ih (evO l true))) L) n

@[expose] noncomputable def getT (d : Nat) (t : PT) : Nat → Nat :=
  PT.rec (motive := fun _ => Nat → Nat) (fun _ => d)
    (fun _ x _ ihl ihr i => Nat.rec (motive := fun _ => Nat) x
      (fun j _ => Bool.rec (motive := fun _ => Nat) (ihr (Nat.div j 2)) (ihl (Nat.div j 2))
        (Nat.beq (Nat.mod j 2) 1)) i) t

@[expose] noncomputable def lenF (l : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun a => a)
    (fun _ _ ih a => CFSG.KC.Loop.strictN (a + 1) ih) l

@[expose] noncomputable def flat (L : List (List Nat)) : List Nat :=
  List.rec (motive := fun _ => List Nat) [] (fun l _ ih => List.append l ih) L

@[expose] noncomputable def getL (L : List (List Nat)) : Nat → List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun x _ ih j => Nat.rec (motive := fun _ => List Nat) x (fun i _ => ih i) j) L

@[expose] noncomputable def incrT (T : PT) (n : Nat) (ord : List Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun i _ ih prev => andB (Nat.blt i n)
      (strictB (getT 0 T i) fun x => andB (Nat.blt prev x) (ih x))) ord

@[expose] noncomputable def distOK (K ord : List Nat) (N : Nat) : Bool :=
  andB (Nat.beq (lenF ord 0) N) (strictB (lenF K 0) fun n => incrT (ofT n K) n ord 0)

@[expose] noncomputable def chunk (mul vec : Nat → Nat → Nat) (vldV : Nat → Bool)
    (A B Bi ONE : Nat) (w1 w2 wi : List Int) (u : Nat) (ms K : List Nat) : Bool :=
  andB (vldV u) (
  strictB (wprod mul A B Bi ONE w1) fun g1 =>
  strictB (wprod mul A B Bi ONE (invW w1)) fun g1i =>
  strictB (wprod mul A B Bi ONE w2) fun g2 =>
  strictB (wprod mul A B Bi ONE (invW w2)) fun g2i =>
  strictB (wprod mul A B Bi ONE (wi ++ 1 :: invW wi)) fun bt =>
  walk mul vec bt ONE u [(g1, g1i), (g2, g2i), (A, A)] ms [] K)

end CFSG.KC.HNFOrb

end
