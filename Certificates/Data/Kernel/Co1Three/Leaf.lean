module

public import Certificates.Data.Kernel.Co1BBound
public import Certificates.Data.Kernel.Co1BW

public section

namespace CFSG.KC.Co1Leaf

open CFSG.KC.Loop CFSG.KLie.CT CFSG.KC.M1F2 CFSG.KC.Co1F2 CFSG.KC.Co1B CFSG.KC.Co1BBound

@[expose] noncomputable def strictL (y : Nat) (k : Nat → List Nat) : List Nat :=
  Nat.rec (motive := fun _ => List Nat) (k (nat_lit 0)) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def strictP (y : Nat) (k : Nat → List (Nat × Nat)) : List (Nat × Nat) :=
  Nat.rec (motive := fun _ => List (Nat × Nat)) (k (nat_lit 0)) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def eltWK (A e : List Nat) : Nat :=
  List.rec (motive := fun _ => List Nat → Nat → Nat) (fun _ acc => acc)
    (fun a _ ih e acc => strictN (mulWK acc (powWK a (List.headD e (nat_lit 0)))) fun x =>
      ih (List.tail e) x)
    A e oneK

@[expose] noncomputable def triK (g : Nat) (L : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) List.nil
    (fun x _ ih => strictL (mulWK x g) fun y => strictL (mulWK y g) fun z =>
      List.cons x (List.cons y (List.cons z ih))) L

@[expose] noncomputable def eltsK (G : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) (fun L => L) (fun g _ ih L => ih (triK g L))
    G (List.cons oneK List.nil)

@[expose] noncomputable def trL (G : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) List.nil
    (fun g _ ih => strictL (trK (nat_lit 24) g) fun t => List.cons t ih) G

@[expose] noncomputable def selK (L : List Nat) (m : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun x _ ih m => nIf(Nat.beq (Nat.land m (nat_lit 1)) (nat_lit 1),
      Nat.xor x (ih (Nat.shiftRight m (nat_lit 1))), ih (Nat.shiftRight m (nat_lit 1)))) L m

@[expose] noncomputable def lowBitK (b : Nat) : Nat := Nat.land b (Nat.xor b (Nat.sub b (nat_lit 1)))

@[expose] noncomputable def crdK (B : List Nat) (v : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat → Nat) (fun _ _ c => c)
    (fun b _ ih v p c => nIf(Nat.beq (Nat.land v (lowBitK b)) (nat_lit 0),
      ih v (Nat.shiftLeft p (nat_lit 1)) c,
      ih (Nat.xor v b) (Nat.shiftLeft p (nat_lit 1)) (Nat.lor c p))) B v (nat_lit 1) (nat_lit 0)

@[expose] noncomputable def gensK (G : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun g _ ih => andB (canK g) (andB (Nat.beq (mulWK g (mulWK g g)) oneK)
      (andB (List.rec (motive := fun _ => Bool) true
        (fun h _ ih2 => andB (Nat.beq (mulWK g h) (mulWK h g)) ih2) G) ih))) G

@[expose] noncomputable def fwK (ET : List Nat) (w : Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) List.nil
    (fun e _ ih => strictL (vmF (nat_lit 24) e w) fun v => List.cons v ih) ET

@[expose] noncomputable def spanK (FW : List Nat) (PT : Nat) (S : List Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun i => Nat.beq i (nat_lit 24))
    (fun s _ ih i => strictB i fun i =>
      andB (Nat.beq (selK FW s) (Nat.xor (pw2 i) (fget PT i (nat_lit 24)))) (ih (Nat.succ i)))
    S (nat_lit 0)

@[expose] noncomputable def basisK (PT : Nat) (B : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun b _ ih => andB (Nat.blt b (pw2 (nat_lit 24))) (andB (Nat.beq (vmF (nat_lit 24) PT b) b) ih)) B

@[expose] noncomputable def crdOK (PT : Nat) (B : List Nat) : Bool :=
  allN (nat_lit 24) fun i => strictB (fget PT i (nat_lit 24)) fun u => strictB (crdK B u) fun c =>
    andB (Nat.blt c (pw2 (lenL B))) (Nat.beq (selK B c) u)

@[expose] noncomputable def testK (XB : Nat → Nat) (PT : Nat) (B : List Nat) (j x : Nat) : Bool :=
  andB (memK XB x) (strictB (vmF (nat_lit 24) PT x) fun px => strictB (crdK B px) fun c =>
    andB (Nat.beq (selK B c) px) (Nat.beq (Nat.shiftRight c j) (nat_lit 1)))

@[expose] noncomputable def lenT (T : List (List Nat)) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ _ ih => Nat.succ ih) T

@[expose] noncomputable def testsK (XB : Nat → Nat) (PT : Nat) (B : List Nat) (T : List (List Nat)) :
    Bool :=
  andB (Nat.beq (lenT T) (lenL B))
    (List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
      (fun xs _ ih j => strictB j fun j => andB
        (List.rec (motive := fun _ => Bool) true (fun x _ ih2 => andB (testK XB PT B j x) ih2) xs)
        (ih (Nat.succ j))) T (nat_lit 0))

@[expose] noncomputable def passK (XB : Nat → Nat) (Z : List Nat) (v : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun z _ ih => andB (memK XB (Nat.xor z v)) ih) Z

@[expose] noncomputable def enumK (XB : Nat → Nat) (Z : List Nat) (B : List Nat) : List Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat → List Nat → List Nat)
    (fun c v _ acc => Bool.rec (motive := fun _ => List Nat) acc (List.cons c acc) (passK XB Z v))
    (fun b _ ih c v p acc => strictL p fun p => strictL (Nat.shiftLeft p (nat_lit 1)) fun p2 =>
      ih c v p2 (strictL (Nat.lor c p) fun c' => strictL (Nat.xor v b) fun v' => ih c' v' p2 acc))
    B (nat_lit 0) (nat_lit 0) (nat_lit 1) List.nil

@[expose] noncomputable def pairsK (PT : Nat) (B : List Nat) (xs : List Nat) : List (Nat × Nat) :=
  List.rec (motive := fun _ => List (Nat × Nat)) List.nil
    (fun x _ ih => strictP (vmF (nat_lit 24) PT x) fun px =>
      List.cons (Prod.mk (Nat.xor x px) (crdK B px)) ih) xs

@[expose] noncomputable def zsK (IM : List Nat) (Q : List (Nat × Nat)) : List Nat :=
  List.rec (motive := fun _ => List Nat) List.nil
    (fun q _ ih => strictL (Nat.xor q.1 (selK IM q.2)) fun z => List.cons z ih) Q

@[expose] noncomputable def imsK (B pre : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) List.nil
    (fun t _ ih => strictL (selK B t) fun v => List.cons v ih) pre

@[expose] noncomputable def extK (pre : List Nat) (cs : List Nat) (acc : List (List Nat)) :
    List (List Nat) :=
  List.rec (motive := fun _ => List (List Nat)) acc
    (fun c _ ih => List.cons (List.append pre (List.cons c List.nil)) ih) cs

@[expose] noncomputable def levelK (XB : Nat → Nat) (B : List Nat) (Q : List (Nat × Nat))
    (P : List (List Nat)) : List (List Nat) :=
  List.rec (motive := fun _ => List (List Nat)) List.nil
    (fun pre _ ih => extK pre (enumK XB (zsK (imsK B pre) Q) B) ih) P

@[expose] noncomputable def searchK (XB : Nat → Nat) (PT : Nat) (B : List Nat)
    (T : List (List Nat)) : List (List Nat) :=
  List.rec (motive := fun _ => List (List Nat) → List (List Nat)) (fun P => P)
    (fun xs _ ih P => ih (levelK XB B (pairsK PT B xs) P)) T (List.cons List.nil List.nil)

@[expose] noncomputable def cubeK (cs : List Nat) : Bool :=
  allN (lenL cs) fun k => strictB (pw2 k) fun u =>
    Nat.beq (selK cs (selK cs (selK cs u))) u

@[expose] noncomputable def allCubeK (P : List (List Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun t _ ih => andB (cubeK t) ih) P

@[expose] noncomputable def leafBodyK (XB : Nat → Nat) (ET : List Nat) (piM w : Nat)
    (S B : List Nat) (T : List (List Nat)) : Bool :=
  strictB (selK ET piM) fun PT =>
    andB (Nat.beq (mulWK PT PT) PT) (andB (Nat.blt w (pw2 (nat_lit 24)))
    (andB (Nat.beq (vmF (nat_lit 24) PT w) (nat_lit 0)) (andB (spanK (fwK ET w) PT S)
    (andB (basisK PT B) (andB (crdOK PT B)
    (andB (testsK XB PT B T) (allCubeK (searchK XB PT B T))))))))

@[expose] noncomputable def leafK (XB : Nat → Nat) (G : List Nat) (piM w : Nat) (S B : List Nat)
    (T : List (List Nat)) : Bool :=
  andB (gensK G) (leafBodyK XB (eltsK (trL G)) piM w S B T)

end CFSG.KC.Co1Leaf

end
