module

public import Certificates.Data.Kernel.Co1B

public section

namespace CFSG.KC.C18005

open CFSG.KC.Co1B

@[expose] noncomputable def andK (a b : Bool) : Bool := Bool.rec (motive := fun _ => Bool) false b a

@[expose] noncomputable def strictB (y : Nat) (k : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k (nat_lit 0)) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def strictL (l : List Nat) (k : List Nat → Bool) : Bool :=
  List.rec (motive := fun _ => (List Nat → List Nat) → Bool) (fun acc => k (acc []))
    (fun x _ ih acc => strictB x fun y => ih fun t => acc (List.cons y t)) l fun t => t

@[expose] noncomputable def allK (n : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun i acc => andK (f i) acc) n

@[expose] noncomputable def chain (Ps : List Nat) (i : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) i (fun P _ ih => pget P ih) Ps

@[expose] noncomputable def symI (t : Nat) : Nat := Nat.mod (Nat.div t 4) 5

@[expose] noncomputable def symJ (t : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (Nat.succ (Nat.mod t 4)) (Nat.mod t 4)
    (Nat.blt (Nat.mod t 4) (symI t))

@[expose] noncomputable def symIdxN (i j : Nat) : Nat :=
  Nat.add (Nat.mul i 4) (Bool.rec (motive := fun _ => Nat) (Nat.sub j 1) j (Nat.blt j i))

@[expose] noncomputable def sgm (t j : Nat) : Nat :=
  Nat.sub (Nat.xor (Nat.succ j)
    (Nat.shiftLeft (Nat.land (Nat.shiftRight (Nat.succ j) (symI t)) 1) (symJ t))) 1

@[expose] noncomputable def blks (B BI : Nat → Nat) (L : List Nat) : Nat → List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun e _ ih jc => Bool.rec (motive := fun _ => List Nat)
      (List.cons (B (Nat.add (Nat.mul 31 (Nat.shiftRight e 1)) jc))
        (ih (sgm (Nat.shiftRight e 1) jc)))
      (List.cons (BI (Nat.add (Nat.mul 31 (Nat.shiftRight e 1)) (sgm (Nat.shiftRight e 1) jc)))
        (ih (sgm (Nat.shiftRight e 1) jc)))
      (Nat.beq (Nat.land e 1) 1)) L

@[expose] noncomputable def fin (L : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun jc => jc)
    (fun e _ ih jc => ih (sgm (Nat.shiftRight e 1) jc)) L

@[expose] noncomputable def par5 (n : Nat) : Nat :=
  Nat.land (Nat.xor (Nat.xor (Nat.xor (Nat.xor n (Nat.shiftRight n 1)) (Nat.shiftRight n 2))
    (Nat.shiftRight n 3)) (Nat.shiftRight n 4)) 1

@[expose] noncomputable def sbit (k j : Nat) : Bool := Nat.beq (par5 (Nat.land (Nat.succ j) k)) 1

@[expose] noncomputable def lettersOK (L : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun e _ ih => andK (Nat.blt e 40) ih) L

@[expose] noncomputable def ptOK (neg : Nat) (Ps : List Nat) (s : Bool) : Bool :=
  allK 240 fun i => Nat.beq (chain Ps i) (Bool.rec (motive := fun _ => Nat) i (pget neg i) s)

@[expose] noncomputable def wordOK (B BI : Nat → Nat) (neg : Nat) (L : List Nat) (k : Nat) : Bool :=
  andK (andK (lettersOK L) (Nat.blt k 32))
    (allK 31 fun j => andK (Nat.beq (fin L j) j)
      (strictL (blks B BI L j) fun Ps => ptOK neg Ps (sbit k j)))

@[expose] noncomputable def kFind (B BI : Nat → Nat) (neg : Nat) (L : List Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun b acc => Nat.add acc
    (Bool.rec (motive := fun _ => Nat) 0 (Nat.shiftLeft 1 b)
      (strictL (blks B BI L (Nat.sub (Nat.shiftLeft 1 b) 1)) fun Ps => ptOK neg Ps true))) 5

@[expose] noncomputable def wordChk (B BI : Nat → Nat) (neg : Nat) (L : List Nat) : Bool :=
  strictB (kFind B BI neg L) (wordOK B BI neg L)

@[expose] noncomputable def lettersB (a : Nat) : List Nat := [Nat.mul 2 a, Nat.mul 2 a]

@[expose] noncomputable def extraC (a b : Nat) : List Nat :=
  Bool.rec (motive := fun _ => List Nat)
    (Bool.rec (motive := fun _ => List Nat) []
      [Nat.succ (Nat.mul 2 (symIdxN (symI b) (symJ a)))] (Nat.beq (symI a) (symJ b)))
    (Bool.rec (motive := fun _ => List Nat)
      [Nat.succ (Nat.mul 2 (symIdxN (symI a) (symJ b)))] [] (Nat.beq (symI a) (symJ b)))
    (Nat.beq (symJ a) (symI b))

@[expose] noncomputable def lettersC (a b : Nat) : List Nat :=
  List.cons (Nat.mul 2 a) (List.cons (Nat.mul 2 b) (List.cons (Nat.succ (Nat.mul 2 a))
    (List.cons (Nat.succ (Nat.mul 2 b)) (extraC a b))))

@[expose] noncomputable def chkC (B BI : Nat → Nat) (neg q : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool) (wordChk B BI neg (lettersC (Nat.div q 20) (Nat.mod q 20)))
    true (andK (Nat.beq (symI (Nat.mod q 20)) (symJ (Nat.div q 20)))
      (Nat.beq (symJ (Nat.mod q 20)) (symI (Nat.div q 20))))

@[expose] noncomputable def baseOK (P : Nat → Nat) (a : Array Nat) (k : Nat) : Bool :=
  (a.toList == (List.range 240).map (pget (P k))) &&
    strictB (P k) fun x => allK 240 fun i => Nat.blt (pget x i) 240

@[expose] noncomputable def pwordT (P : Nat → Nat) (w : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) pidK (fun r _ ih => pcomp (P r) ih) w

@[expose] noncomputable def genOK (w : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun r _ ih => andK (Nat.blt r 12) ih) w

@[expose] noncomputable def blkOK (P B : Nat → Nat) (bw : Array (Array (Bool × List Nat)))
    (q : Nat) : Bool :=
  Prod.rec (motive := fun _ => Bool) (fun s w => andK (genOK w)
      (Nat.beq (B q) (Bool.rec (motive := fun _ => Nat) (pwordT P w) (pcomp (P 12) (pwordT P w)) s)))
    ((bw.getD (q / 31) #[]).getD (q % 31) (false, []))

@[expose] noncomputable def invOK (B BI : Nat → Nat) (q : Nat) : Bool :=
  strictB (BI q) fun x => andK (allK 240 fun i => Nat.blt (pget x i) 240)
    (Nat.beq (pcomp (B q) x) pidK)

end CFSG.KC.C18005
