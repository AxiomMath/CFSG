module

public import Certificates.Data.Kernel.C21205.Sylow

public section

namespace CFSG.KC.C21205

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc CFSG.KC.Misc.G24
open CFSG.LargeExtraspecial.AS35QCo.Native (idc)

@[expose] noncomputable def powK (c e : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) idc (fun _ acc => mulK acc c) e

@[expose] noncomputable def xorB (a b : Bool) : Bool := Bool.rec (motive := fun _ => Bool) b (notB b) a

@[expose] noncomputable def newL (v : Nat) (L : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x _ ih => andB (notB (Nat.beq v x)) ih) L

@[expose] noncomputable def memL (c : Nat) (S : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun x _ ih => orB (Nat.beq c x) ih) S

@[expose] noncomputable def sevenW (F : List Nat) (y : Nat) : Nat → List Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → List Nat → Nat → Bool)
    (fun _ _ n => Nat.ble 7 n)
    (fun e _ ih m acc n => Bool.rec (motive := fun _ => Bool)
      (ih (Nat.shiftRight m 1) acc n)
      (letB (mulK (mulK (fld e 36 0) y) (fld (Nat.shiftRight e 36) 36 0)) fun v =>
        andB (newL v acc) (letB (Nat.succ n) fun n' => ih (Nat.shiftRight m 1) (List.cons v acc) n'))
      (Nat.beq (Nat.land m 1) 1)) F

@[expose] noncomputable def sevenK (F : List Nat) (y m : Nat) : Bool :=
  sevenW F y m (List.cons y List.nil) 1

@[expose] noncomputable def ncW (W : List Nat) (y : Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => false)
    (fun e _ ih m => orB (andB (Nat.beq (Nat.land m 1) 1)
      (letB (Nat.shiftRight e 72) fun u => notB (Nat.beq (mulK y u) (mulK u y))))
      (ih (Nat.shiftRight m 1))) W

@[expose] noncomputable def testK (r : Nat) (F W S : List Nat) (c t p : Nat) : Bool :=
  orB (andB (Nat.beq t 0) (orB (Nat.beq c idc) (Nat.beq c r))) <|
  orB (andB (Nat.beq t 1) (xorB (Nat.beq (powK c p) idc) (Nat.beq (powK (mulK r c) p) idc))) <|
  orB (andB (Nat.beq t 2) (sevenK F c p)) <|
  orB (andB (Nat.beq t 3) (memL c S)) (andB (Nat.beq t 4) (ncW W c p))

@[expose] noncomputable def entryK (r nA A B : Nat) (F W S : List Nat) (x : Nat) : Bool :=
  letB (fld x 36 0) fun c => letB (fld (Nat.shiftRight x 36) 6 0) fun i =>
    letB (fld (Nat.shiftRight x 42) 9 0) fun j => letB (fld (Nat.shiftRight x 51) 3 0) fun t =>
      letB (Nat.shiftRight x 54) fun p => andB (Nat.blt i nA) <|
        andB (Nat.beq c (mulK (fld (fld A 72 i) 36 0) (fld (fld B 72 j) 36 0))) (testK r F W S c t p)

@[expose] noncomputable def chunkK (r nA A B : Nat) (F W S L : List Nat) : Bool :=
  allL L (entryK r nA A B F W S)

@[expose] noncomputable def facK (r n A : Nat) : Bool :=
  allN n fun i => letB (fld A 72 i) fun e => letB (fld e 36 0) fun g =>
    andB (pairK g (Nat.shiftRight e 36)) (Nat.beq (mulK g r) (mulK r g))

@[expose] noncomputable def scanK (r : Nat) (S L : List Nat) : Bool :=
  allL L fun x => letB (fld x 36 0) fun d =>
    allL S fun s => notB (Nat.beq (mulK d s) (mulK (mulK r s) d))

@[expose] noncomputable def orbW (r : Nat) (O : List Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun x _ ih lo => letB (fld x 36 0) fun m => letB (Nat.shiftRight x 36) fun mi =>
      letB (mulK (mulK m r) mi) fun v => andB (pairK m mi) (andB (Nat.ble lo v) (ih (Nat.succ v))))
    O

@[expose] noncomputable def orbK (r : Nat) (O : List Nat) : Bool := orbW r O 0

@[expose] noncomputable def fK (r : Nat) (F : List Nat) : Bool :=
  allL F fun e => letB (fld e 36 0) fun g =>
    andB (pairK g (fld (Nat.shiftRight e 36) 36 0)) (Nat.beq (mulK g r) (mulK r g))

@[expose] noncomputable def wK (r : Nat) (W : List Nat) : Bool :=
  allL W fun e => letB (fld e 36 0) fun g =>
    andB (pairK g (fld (Nat.shiftRight e 36) 36 0))
      (andB (Nat.beq (mulK g r) (mulK r g)) (Nat.beq (Nat.shiftRight e 72) (powK g 60)))

@[expose] noncomputable def strictC (L : List Nat) (k : Nat → Nat → Bool) : Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Nat → Bool) k
    (fun x _ ih lo n => letB (fld x 36 0) fun c =>
      andB (Nat.ble lo c) (letB (Nat.succ n) fun n' => ih (Nat.succ c) n')) L

@[expose] noncomputable def strictD (D : List (List Nat)) (N : Nat) : Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Nat → Bool) (fun _ n => Nat.beq n N)
    (fun L _ ih => strictC L ih) D

@[expose] noncomputable def globK (D : List (List Nat)) (N : Nat) : Bool := strictD D N 0 0

@[expose] noncomputable def critK (r nA A B : Nat) (O F W : List Nat) (D : List (List Nat))
    (N : Nat) : Bool :=
  andB (orbK r O) <| andB (fK r F) <| andB (wK r W) <| andB (facK r nA A) <|
    andB (facK r 512 B) <| andB (globK D N) (Nat.beq (Nat.mul (List.length O) N) 1451520)

@[expose] noncomputable def chunkAt (D : List (List Nat)) (i : Nat) : List Nat :=
  List.getD D i List.nil

end CFSG.KC.C21205

end
