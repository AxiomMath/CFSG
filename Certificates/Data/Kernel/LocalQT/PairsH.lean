module

public import Certificates.Data.Kernel.LocalQT.Pairs
public import Certificates.Data.Kernel.LocalQT.LatM

public section

namespace CFSG.KC.LQT.PH

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.LQT.L CFSG.KC.LQT.T2

@[expose] noncomputable def hP : Nat := 2305843009213693951

@[expose] noncomputable def encK (n x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun k acc => Nat.add (Nat.mul acc n) (img x (Nat.sub (Nat.sub n 1) k))) n

@[expose] noncomputable def hkK (x : Nat) : Nat := Nat.mod (encK 24 x) hP

@[expose] noncomputable def colFrom (n : Nat) (C : List Lvl) (f : Nat → Nat) (s : Nat → Bool) :
    Nat → List Nat → List Nat :=
  List.rec (motive := fun _ => Nat → List Nat → List Nat)
    (fun p acc => letL (f p) fun h => Bool.rec (motive := fun _ => List Nat) acc
      (List.cons h acc) (s h))
    (fun lv _ ih p acc => Nat.rec (motive := fun _ => List Nat) acc
      (fun j accJ => Bool.rec (motive := fun _ => List Nat)
        (letL (mul n p (CFSG.KC.LQT.S.getK lv.2.1 j)) fun q => ih q accJ) accJ
        (Nat.beq (CFSG.KC.LQT.S.getK lv.2.1 j) 0)) n) C

@[expose] noncomputable def colAll (n : Nat) (C : List Lvl) (f : Nat → Nat) (s : Nat → Bool) :
    List Nat :=
  colFrom n C f s (one n) []

@[expose] noncomputable def inRange (R r h : Nat) : Bool := Nat.beq (Nat.div (Nat.mul h R) hP) r

@[expose] noncomputable def hkR (n : Nat) (C : List Lvl) (R r : Nat) : Bool :=
  sincK (CFSG.KC.LQT.Syl.sortN (colAll n C hkK (inRange R r)))

@[expose] noncomputable def allReps (C : List Lvl) : List Nat :=
  List.flatten (List.map (fun lv => CFSG.KC.LQT.S.filtL lv.2.1 fun u => notB (Nat.beq u 0)) C)

@[expose] noncomputable def simsK (n : Nat) (C : List Lvl) (S : List Nat) : Bool :=
  List.rec (motive := fun _ => List Nat → Bool)
    (fun prev => allL S fun s => impB (allL prev fun b => Nat.beq (img s b) b) (Nat.beq s (one n)))
    (fun lv C' ih prev => andB
      (allL S fun s => impB (allL prev fun b => Nat.beq (img s b) b)
        (allL (CFSG.KC.LQT.S.filtL lv.2.1 fun u => notB (Nat.beq u 0)) fun u =>
          inC n (List.cons lv C') (chainF (List.cons lv C')) (mul n s u)))
      (ih (List.cons lv.1 prev))) C []

@[expose] noncomputable def grpS (n : Nat) (C : List Lvl) (F : Nat) (G : List Nat)
    (W : List (List (List Nat))) (d : Nat) : Bool :=
  andB (allL G (inC n C F)) (andB (wordsC n C G W d) (simsK n C (List.append G (allReps C))))

@[expose] noncomputable def posReps (n : Nat) (lv : Lvl) : List Nat :=
  List.map (fun d => Nat.rec (motive := fun _ => Nat) 0
      (fun j acc => Bool.rec (motive := fun _ => Nat) acc (CFSG.KC.LQT.S.getK lv.2.1 j)
        (andB (Nat.beq (CFSG.KC.LQT.S.getK lv.2.2.1 j) d)
          (notB (Nat.beq (CFSG.KC.LQT.S.getK lv.2.1 j) 0))))
    n) (List.range lv.2.2.2)

@[expose] noncomputable def lastK (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun x t ih => List.rec (motive := fun _ => Nat) x (fun _ _ _ => ih) t) l

@[expose] noncomputable def prodIdx (n : Nat) (C : List Lvl) (PR : List (List Nat)) (i : Nat) :
    Nat :=
  List.rec (motive := fun _ => List (List Nat) → Nat → Nat) (fun _ _ => one n)
    (fun lv _ ih PR i =>
      mul n (CFSG.KC.LQT.S.getK (CFSG.KC.LQT.Syl.getK PR 0 []) (Nat.mod i lv.2.2.2))
        (ih (List.tail PR) (Nat.div i lv.2.2.2))) C PR i

@[expose] noncomputable def hkDBlk (n : Nat) (C : List Lvl) (PR : List (List Nat))
    (I : List (List Nat)) (k : Nat) : Bool :=
  andB (Nat.blt 0 (CFSG.KC.LQT.S.lenL (CFSG.KC.LQT.Syl.getK I k [])))
    (sincK (List.map (fun i => hkK (prodIdx n C PR i)) (List.append
      (Bool.rec (motive := fun _ => List Nat)
        [lastK (CFSG.KC.LQT.Syl.getK I (Nat.sub k 1) [])] [] (Nat.beq k 0))
      (CFSG.KC.LQT.Syl.getK I k []))))

@[expose] noncomputable def cntFrom (n : Nat) (C : List Lvl) (f : Nat → Bool) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat)
    (fun p => Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 1) (f p))
    (fun lv _ ih p => Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun j acc => Nat.add acc (Bool.rec (motive := fun _ => Nat)
        (CFSG.KC.LQT.Syl.letN (mul n p (CFSG.KC.LQT.S.getK lv.2.1 j)) ih) (nat_lit 0)
        (Nat.beq (CFSG.KC.LQT.S.getK lv.2.1 j) 0))) n) C

@[expose] noncomputable def cntChunk (n : Nat) (C : List Lvl) (f : Nat → Bool) (j : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 1)
      (Bool.rec (motive := fun _ => Bool) false (f (one n)) (Nat.beq j 0)))
    (fun lv C' _ => Bool.rec (motive := fun _ => Nat)
      (CFSG.KC.LQT.Syl.letN (mul n (one n) (CFSG.KC.LQT.S.getK lv.2.1 j)) (cntFrom n C' f))
      (nat_lit 0) (Nat.beq (CFSG.KC.LQT.S.getK lv.2.1 j) 0)) C

@[expose] noncomputable def fiveK (f : Nat → Nat) (Q : List Nat) : Bool :=
  List.rec (motive := fun _ => List Nat → Bool) (fun _ => false)
    (fun q _ ih seen => letB (f q) fun v => Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool) (ih (List.cons v seen)) true
        (Nat.beq (CFSG.KC.LQT.S.lenL seen) 4))
      (ih seen) (CFSG.KC.LQT.S.memL v seen)) Q []

abbrev Blk := Nat × List Nat

@[expose] noncomputable def flatB (B : List Blk) : List Nat := List.flatten (List.map Prod.snd B)

@[expose] noncomputable def memB (y : Nat) (B : List Blk) : Bool :=
  List.rec (motive := fun _ => Bool) false
    (fun b _ ih => Bool.rec (motive := fun _ => Bool) ih (CFSG.KC.LQT.S.memL y b.2)
      (Nat.ble y b.1)) B

@[expose] noncomputable def sortedB (s : Nat) (B : List Blk) : Bool :=
  andB (sincK (flatB B)) (andB (allA B fun b => Nat.beq b.1 (lastK b.2))
    (List.rec (motive := fun _ => Bool) true
      (fun b t ih => andB (Bool.rec (motive := fun _ => Bool)
        (Nat.beq (CFSG.KC.LQT.S.lenL b.2) s) (Nat.ble (CFSG.KC.LQT.S.lenL b.2) s)
        (List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) t)) ih) B))

@[expose] noncomputable def getB (B : List Blk) (s i : Nat) : Nat :=
  CFSG.KC.LQT.S.getK (CFSG.KC.LQT.Syl.getK B (Nat.div i s) (0, [])).2 (Nat.mod i s)

@[expose] noncomputable def getT (T : List (List (Nat × Nat × Nat))) (s i : Nat) :
    Nat × Nat × Nat :=
  CFSG.KC.LQT.Syl.getK (CFSG.KC.LQT.Syl.getK T (Nat.div i s) []) (Nat.mod i s) (0, 0, 0)

@[expose] noncomputable def zipB (l : List Nat) (t : List (Nat × Nat × Nat))
    (f : Nat → Nat × Nat × Nat → Bool) : Bool :=
  List.rec (motive := fun _ => List (Nat × Nat × Nat) → Bool)
    (fun t => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) t)
    (fun x _ ih t => List.rec (motive := fun _ => Bool) false
      (fun e t' _ => andB (f x e) (ih t')) t)
    l t

@[expose] noncomputable def blkOK (op : Nat → Nat → Nat) (z : Nat) (G : List Nat) (s N : Nat)
    (B : List Blk) (T : List (List (Nat × Nat × Nat))) (b : Nat) : Bool :=
  zipB (CFSG.KC.LQT.Syl.getK B b (0, [])).2 (CFSG.KC.LQT.Syl.getK T b []) fun x e =>
    andB (allL G fun g => memB (op g x) B)
      (Bool.rec (motive := fun _ => Bool)
        (andB (andB (Nat.blt e.1 N) (Nat.blt e.2.1 (CFSG.KC.LQT.S.lenL G)))
          (andB (Nat.beq (op (CFSG.KC.LQT.S.getK G e.2.1) (getB B s e.1)) x)
            (Nat.beq (Nat.succ (getT T s e.1).2.2) e.2.2)))
        (Nat.beq x z) (Nat.beq e.2.2 0))

@[expose] noncomputable def blkRange (op : Nat → Nat → Nat) (z : Nat) (G : List Nat) (s N : Nat)
    (B : List Blk) (T : List (List (Nat × Nat × Nat))) (lo k : Nat) : Bool :=
  allN k fun i => blkOK op z G s N B T (Nat.add lo i)

@[expose] noncomputable def hkB (B : List Blk) (R r : Nat) : Bool :=
  sincK (CFSG.KC.LQT.Syl.sortN (CFSG.KC.LQT.S.filtL (List.map hkK (flatB B)) (inRange R r)))

@[expose] noncomputable def orbMask (A : List Nat) (i : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun a _ ih => Nat.lor (Nat.shiftLeft 1 (img a i)) ih) A

@[expose] noncomputable def packK (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun m _ ih acc => CFSG.KC.LQT.Syl.letN (Nat.add (Nat.mul acc 16777216) m) ih) l 0

@[expose] noncomputable def unpackK (t : Nat) : List Nat :=
  (Nat.rec (motive := fun _ => Nat × List Nat → Nat × List Nat) (fun st => st)
    (fun _ ih st => Bool.rec (motive := fun _ => Nat × List Nat)
      (ih (Nat.shiftRight st.1 24, List.cons (Nat.land st.1 16777215) st.2)) st
      (Nat.beq st.1 0)) 24 (t, [])).2

@[expose] noncomputable def imgMask (n g m : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Bool.rec (motive := fun _ => Nat) acc (Nat.lor acc (Nat.shiftLeft 1 (img g i)))
      (Nat.beq (Nat.land (Nat.shiftRight m i) 1) 1)) n

@[expose] noncomputable def actTK (n g t : Nat) : Nat :=
  packK (CFSG.KC.LQT.Syl.dedupS (CFSG.KC.LQT.Syl.sortN (List.map (imgMask n g) (unpackK t))))

@[expose] noncomputable def trioK (n : Nat) (A : List Nat) : Nat :=
  packK (CFSG.KC.LQT.Syl.dedupS (CFSG.KC.LQT.Syl.sortN (List.map (orbMask A) (List.range n))))

end CFSG.KC.LQT.PH

end
