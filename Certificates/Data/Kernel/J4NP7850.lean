module

public import Certificates.Data.Kernel.J4M4F.Defs

public section

namespace CFSG.KD.J4NP7850

open CFSG.KC.Loop CFSG.KC.J4Q CFSG.KD.J4M4F

@[expose] noncomputable def y8Lk : List Nat :=
  [0, 12, 16, 28, 129, 141, 145, 157, 352, 364, 368, 380, 481, 493, 497, 509, 576, 588, 592,
    604, 705, 717, 721, 733, 800, 812, 816, 828, 929, 941, 945, 957, 1060, 1064, 1076, 1080,
    1189, 1193, 1205, 1209, 1348, 1352, 1364, 1368, 1477, 1481, 1493, 1497, 1636, 1640, 1652,
    1656, 1765, 1769, 1781, 1785, 1796, 1800, 1812, 1816, 1925, 1929, 1941, 1945]

@[expose] noncomputable def y8Bk : List Nat := [12, 16, 129, 352, 576, 1060]

@[expose] noncomputable def cBk : List Nat := [1, 2, 4, 32, 64]

@[expose] noncomputable def memK (x : Nat) (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun y _ ih => orB (Nat.beq x y) ih) l

@[expose] noncomputable def allL (l : List Nat) (f : Nat → Bool) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun y _ ih => andB (f y) ih) l

@[expose] noncomputable def combK (B : List Nat) (n s : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun t acc => Bool.rec (motive := fun _ => Nat) acc (Nat.xor acc (getN 0 B t))
      (Nat.beq (Nat.land (Nat.shiftRight s t) 1) 1)) n

@[expose] noncomputable def inSpanK (B : List Nat) (n x : Nat) : Bool :=
  notB (allR (Nat.shiftLeft 1 n) fun s => neN (combK B n s) x)

@[expose] noncomputable def etaV (rm : Nat) (Us : List Nat) (c v : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) v
    (fun j acc => Bool.rec (motive := fun _ => Nat) acc (vecJ rm acc (getN 0 Us j))
      (Nat.beq (Nat.land (Nat.shiftRight c j) 1) 1)) (nat_lit 11)

@[expose] noncomputable def piK (rm G : Nat) (PV KW : List Nat) : Bool :=
  allR 31 fun k => strictB (getN 0 PV k) fun p =>
    andB (Nat.blt p (Nat.shiftLeft 1 112)) (Nat.beq (vecJ rm p G) (getN 0 KW k))

@[expose] noncomputable def y8FixK (rm : Nat) (Us PV B : List Nat) : Bool :=
  allR 6 fun t => allR 31 fun k => strictB (getN 0 PV k) fun p =>
    Nat.beq (etaV rm Us (getN 0 B t) p) p

@[expose] noncomputable def y8MoveK (rm : Nat) (Us PV C MW : List Nat) : Bool :=
  allR 31 fun s => strictB (getN 0 MW s) fun k => strictB (getN 0 PV k) fun p =>
    andB (Nat.blt k 31) (neN (etaV rm Us (combK C 5 (Nat.succ s)) p) p)

@[expose] noncomputable def y8DecK (L B C Pr : List Nat) : Bool :=
  andB (allR 64 fun s => memK (combK B 6 s) L)
    (andB (allL L fun y => inSpanK B 6 y)
      (allR 11 fun j => strictB (getN 0 Pr j) fun x =>
        andB (inSpanK C 5 x) (memK (Nat.xor (Nat.shiftLeft 1 j) x) L)))

@[expose] noncomputable def moveK (rm : Nat) (Us PV : List Nat) (k : Nat) : Bool :=
  andB (Nat.blt k 31) (strictB (etaV rm Us 4 (getN 0 PV k)) fun v =>
    allR 31 fun k' => neN v (getN 0 PV k'))

@[expose] noncomputable def packR (r : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun x _ ih => Nat.lor x (Nat.shiftLeft ih 11)) r

@[expose] noncomputable def actP (T c : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun j acc => Bool.rec (motive := fun _ => Nat) acc
      (Nat.xor acc (Nat.land (Nat.shiftRight T (Nat.mul 11 j)) 2047))
      (Nat.beq (Nat.land (Nat.shiftRight c j) 1) 1)) (nat_lit 11)

@[expose] noncomputable def wimgP (TP w : List Nat) (m : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) m (fun i _ ih => strictN ih fun x => actP (getN 0 TP i) x) w

@[expose] noncomputable def imgP (TP w B : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) [] (fun b _ ih => List.cons (wimgP TP w b) ih) B

@[expose] noncomputable def spanL (B : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) [0]
    (fun b _ ih => List.rec (motive := fun _ => List Nat → List Nat) (fun acc => acc)
      (fun x _ ih2 acc => ih2 (List.cons (Nat.xor x b) acc)) ih ih) B

@[expose] noncomputable def indK (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun x _ ih => Nat.lor ih (Nat.shiftLeft 1 x)) l

@[expose] noncomputable def wOK (w : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun i _ ih => andB (Nat.blt i 6) ih) w

@[expose] noncomputable def orbK (TP B : List Nat) (W : List (List Nat)) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun w _ ih prev => strictB (indK (spanL (imgP TP w B))) fun k =>
      andB (wOK w) (andB (Nat.blt prev k) (ih k))) W 0

@[expose] noncomputable def rankK (c rm one : Nat) (FM R : List Nat) (Q : Nat) : Bool :=
  Nat.beq (Nat.rec (motive := fun _ => Nat) Q
    (fun j acc => strictN acc fun a => Nat.xor a
      (mulJ c rm (Nat.xor (getN one FM j) one) (getN 0 R j))) (nat_lit 10)) one

@[expose] noncomputable def kwFixK (rm one : Nat) (FM KW : List Nat) : Bool :=
  allR 10 fun j => strictB (getN one FM j) fun M => allR 31 fun k => strictB (getN 0 KW k) fun v =>
    Nat.beq (vecJ rm v M) v

@[expose] noncomputable def qK (rm : Nat) (P : List Nat) (Q : Nat) : Bool :=
  Nat.beq (List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun p _ ih => Nat.lor ih (Nat.shiftLeft (rowJ rm Q p) (Nat.mul (nat_lit 128) p))) P) Q

@[expose] noncomputable def basisK (rm one : Nat) (FM P B : List Nat) : Bool :=
  andB (allR 6 fun s => Nat.blt (getN 0 P s) 112)
  (allR 6 fun t => strictB (getN 0 B t) fun v =>
    andB (Nat.blt v (Nat.shiftLeft 1 112))
    (andB (allR 10 fun j => Nat.beq (vecJ rm v (getN one FM j)) v)
      (allR 6 fun s => Nat.beq (Nat.land (Nat.shiftRight v (getN 0 P s)) 1)
        (Bool.rec (motive := fun _ => Nat) 0 1 (Nat.beq s t)))))

@[expose] noncomputable def spanK (B K U : List Nat) : Bool :=
  allR 63 fun s => strictB (combK B 6 (Nat.succ s)) fun v => orB (memK v K) (memK v U)

@[expose] noncomputable def nsK (x : Nat) (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun y _ ih => Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool) ih false (Nat.beq x y)) true (Nat.blt x y)) l

@[expose] noncomputable def ltHead (x : Nat) (chs : List (List Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun ch _ _ => List.rec (motive := fun _ => Bool) true (fun y _ _ => Nat.blt x y) ch) chs

@[expose] noncomputable def ninC (x : Nat) (chs : List (List Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun ch rest ih => Bool.rec (motive := fun _ => Bool) ih (nsK x ch) (ltHead x rest)) chs

@[expose] noncomputable def othVK (rm G : Nat) (U Qs : List Nat) : Bool :=
  allR 32 fun i => Nat.beq (vecJ rm (getN 0 Qs i) G) (getN 0 U i)

@[expose] noncomputable def othSK (R0 : Nat) (Qs : List Nat) (S5 S6 : List (List Nat)) : Bool :=
  allR 32 fun i => strictB (getN 0 Qs i) fun x =>
    andB (neN x R0) (andB (ninC x S5) (ninC x S6))

@[expose] noncomputable def duadK (c rm one G : Nat) (FM : List Nat) (U4 : Nat) : Bool :=
  strictB (fRK c rm one FM 420) fun f => Nat.beq (mulJ c rm G f) (mulJ c rm U4 G)

end CFSG.KD.J4NP7850
