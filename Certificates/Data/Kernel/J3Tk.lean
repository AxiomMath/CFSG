module

public import CFSG.Certificates.Kernel.Enum.Defs
public import CFSG.RankThree.PartTwo.Sec8.Hering611S4Tab
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.Sporadic.SmallOddCore.J3

public section

namespace CFSG.KC.J3Tk

open CFSG.KC.Enum CFSG.Sporadic.Th.Native CFSG.RankThree.PartTwo.Sec8.Hering611.J3T

@[expose] noncomputable def ap (T q : Nat) : Nat := pg (nat_lit 13) (nat_lit 8191) T q

@[expose] noncomputable def pc (p q : Nat) : Nat := pcomp (nat_lit 6156) (nat_lit 13) (nat_lit 8191) p q

@[expose] noncomputable def pid : Nat := pidn (nat_lit 6156) (nat_lit 13)

@[expose] noncomputable def pw (p e : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) pid (fun _ ih => strictN ih (fun q => pc p q)) e

@[expose] noncomputable def kf (k t : Nat) : Nat :=
  Nat.land (Nat.shiftRight k (Nat.mul (nat_lit 13) t)) (nat_lit 8191)

@[expose] noncomputable def k4 (a b c d : Nat) : Nat :=
  Nat.lor a (Nat.lor (Nat.shiftLeft b (nat_lit 13))
    (Nat.lor (Nat.shiftLeft c (nat_lit 26)) (Nat.shiftLeft d (nat_lit 39))))

@[expose] noncomputable def keyF (f : Nat → Nat) : Nat :=
  k4 (f (nat_lit 0)) (f (nat_lit 1)) (f (nat_lit 3)) (f (nat_lit 2))

@[expose] noncomputable def keyL (g k : Nat) : Nat :=
  k4 (ap g (kf k (nat_lit 0))) (ap g (kf k (nat_lit 1))) (ap g (kf k (nat_lit 2)))
    (ap g (kf k (nat_lit 3)))

@[expose] noncomputable def key1 : Nat := k4 (nat_lit 0) (nat_lit 1) (nat_lit 3) (nat_lit 2)

@[expose] noncomputable def allB (f : Nat → Bool) : Bool :=
  bAnd(f (nat_lit 0), bAnd(f (nat_lit 1), bAnd(f (nat_lit 3), f (nat_lit 2))))

@[expose] noncomputable def nth (l : List Nat) (j : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun a _ ih j => Nat.rec (motive := fun _ => Nat) a (fun i _ => ih i) j) l j

@[expose] noncomputable def len (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ _ ih => Nat.succ ih) l

@[expose] noncomputable def val (RT MT : Nat → Nat) (c : Nat) : Nat :=
  Bool.rec (Bool.rec (RT (Nat.sub (Nat.shiftRight c (nat_lit 1)) (nat_lit 1)))
      (MT (Nat.shiftRight c (nat_lit 1))) (Nat.beq (Nat.land c (nat_lit 1)) (nat_lit 1)))
    pid (Nat.beq c (nat_lit 0))

@[expose] noncomputable def opOK (PR : Nat) (k i x : Nat) : Bool :=
  bAnd(Nat.blt x (nat_lit 109),
    Bool.rec (Bool.rec (Nat.blt (kf PR x) i) true (Nat.blt x (nat_lit 19))) true (Nat.beq x k))

@[expose] noncomputable def stepV (RT MT : Nat → Nat) (k e v op a b : Nat) : Nat :=
  (fun sa => Bool.rec (Bool.rec (val RT MT e) (pw sa b) (Nat.beq op (nat_lit 1)))
      (pc sa (Bool.rec (RT b) v (Nat.beq b k))) (Nat.beq op (nat_lit 0)))
    (Bool.rec (RT a) v (Nat.beq a k))

@[expose] noncomputable def stepOK (RT MT : Nat → Nat) (PR k i e v op a b : Nat) : Bool :=
  bAnd(Nat.blt op (nat_lit 3), bAnd(opOK PR k i a,
    Bool.rec (Bool.rec
        ((fun sa => (fun V => bAnd(Nat.beq (pc sa V) pid, Nat.beq (pc V sa) pid)) (val RT MT e))
          (Bool.rec (RT a) v (Nat.beq a k)))
        true (Nat.beq op (nat_lit 1)))
      (opOK PR k i b) (Nat.beq op (nat_lit 0))))

@[expose] noncomputable def runK (RT MT : Nat → Nat) (PR k i e : Nat) :
    List (Nat × Nat × Nat) → Nat → Bool :=
  fun l => List.rec (motive := fun _ => Nat → Bool)
    (fun v => Nat.beq v (val RT MT e))
    (fun ins _ ih v => Prod.rec (motive := fun _ => Bool) (fun op ab => Prod.rec
        (motive := fun _ => Bool) (fun a b => bAnd(stepOK RT MT PR k i e v op a b,
          strictB (stepV RT MT k e v op a b) ih)) ab) ins) l

@[expose] noncomputable def chunkK (RT MT : Nat → Nat) (PR PM NM i : Nat)
    (c : Nat × Nat × Nat × List (Nat × Nat × Nat)) : Bool :=
  Prod.rec (motive := fun _ => Bool) (fun k r => Prod.rec (motive := fun _ => Bool) (fun s r =>
    Prod.rec (motive := fun _ => Bool) (fun e ins =>
      bAnd(Nat.ble (nat_lit 19) k, bAnd(Nat.blt k (nat_lit 109),
      bAnd(Bool.rec (Bool.rec false (bAnd(Nat.blt (Nat.shiftRight s (nat_lit 1)) NM,
            Nat.blt (kf PM (Nat.shiftRight s (nat_lit 1))) i))
          (Nat.beq (Nat.land s (nat_lit 1)) (nat_lit 1))) true (Nat.beq s (nat_lit 0)),
      bAnd(Bool.rec
          (bAnd(Nat.beq (Nat.sub (Nat.shiftRight e (nat_lit 1)) (nat_lit 1)) k,
            bAnd(Nat.ble (nat_lit 2) e, Nat.beq (kf PR k) i)))
          (bAnd(Nat.blt (Nat.shiftRight e (nat_lit 1)) NM,
            Nat.beq (kf PM (Nat.shiftRight e (nat_lit 1))) i))
          (Nat.beq (Nat.land e (nat_lit 1)) (nat_lit 1)),
        Nat.beq (strictN (val RT MT s)
          (fun v => Bool.rec (nat_lit 0) (nat_lit 1) (runK RT MT PR k i e ins v))) (nat_lit 1)))))) r)
    r) c

@[expose] noncomputable def chunksK (RT MT : Nat → Nat) (PR PM NM : Nat) :
    List (Nat × Nat × Nat × List (Nat × Nat × Nat)) → Nat → Bool :=
  fun l => List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun c _ ih i => bAnd(chunkK RT MT PR PM NM i c, ih (Nat.succ i))) l

@[expose] noncomputable def endOf (c : Nat × Nat × Nat × List (Nat × Nat × Nat)) : Nat :=
  Prod.rec (motive := fun _ => Nat) (fun _ r => Prod.rec (motive := fun _ => Nat)
    (fun _ r => Prod.rec (motive := fun _ => Nat) (fun e _ => e) r) r) c

@[expose] noncomputable def ends (l : List (Nat × Nat × Nat × List (Nat × Nat × Nat))) :
    List Nat :=
  List.rec (motive := fun _ => List Nat) [] (fun c _ ih => endOf c :: ih) l

@[expose] noncomputable def coverK (PR : Nat) (E : List Nat) : Bool :=
  allBlk (nat_lit 19) (fun k => Nat.beq (nth E (kf PR k)) (Nat.add (Nat.mul 2 k) 2)) (nat_lit 90)

@[expose] noncomputable def coverM (PM NM : Nat) (E : List Nat) : Bool :=
  allBlk (nat_lit 0) (fun m => Nat.beq (nth E (kf PM m)) (Nat.add (Nat.mul 2 m) 1)) NM

@[expose] noncomputable def keyAt (K i : Nat) : Nat :=
  Nat.land (Nat.shiftRight K (Nat.mul (nat_lit 52) i)) (nat_lit 4503599627370495)

@[expose] noncomputable def memK (K SR N t : Nat) : Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => false) (fun _ ih lo hi =>
    Bool.rec
      ((fun mid => (fun v => Bool.rec (Bool.rec (ih lo mid) (ih (Nat.succ mid) hi) (Nat.blt v t))
        true (Nat.beq v t)) (keyAt K (kf SR mid))) (Nat.shiftRight (Nat.add lo hi) (nat_lit 1)))
      false (Nat.ble hi lo)) (nat_lit 14) (nat_lit 0) N

@[expose] noncomputable def atE (G : Nat → Nat) (PA LA i p : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ p => p)
    (fun _ ih i p => Bool.rec (ap (G (kf LA i)) (ih (kf PA i) p)) p (Nat.beq i (nat_lit 0))) i i p

@[expose] noncomputable def atIE (GI : Nat → Nat) (PA LA i p : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ p => p)
    (fun _ ih i p => Bool.rec (ih (kf PA i) (ap (GI (kf LA i)) p)) p (Nat.beq i (nat_lit 0))) i i p

@[expose] noncomputable def gensOf (D : TData) (e : Nat) : List Nat := (D.enums.getD e ([], 0)).1

@[expose] noncomputable def cardOf (D : TData) (e : Nat) : Nat := (D.enums.getD e ([], 0)).2

@[expose] noncomputable def entK (G : Nat → Nat) (m K PA LA i : Nat) : Bool :=
  bAnd(Nat.blt (kf PA i) i, bAnd(Nat.blt (kf LA i) m,
    Nat.beq (keyAt K i) (keyL (G (kf LA i)) (keyAt K (kf PA i)))))

@[expose] noncomputable def srtK (N K SR j : Nat) : Bool :=
  bAnd(Nat.blt (kf SR j) N, bAnd(Nat.blt (kf SR (Nat.succ j)) N,
    Nat.blt (keyAt K (kf SR j)) (keyAt K (kf SR (Nat.succ j)))))

@[expose] noncomputable def cloK (G : Nat → Nat) (m N K SR i : Nat) : Bool :=
  allBlk (nat_lit 0) (fun j => memK K SR N (keyL (G j) (keyAt K i))) m

@[expose] noncomputable def gT (RT : Nat → Nat) (gl : List Nat) (j : Nat) : Nat := RT (nth gl j)

@[expose] noncomputable def gTI (RT : Nat → Nat) (gl : List Nat) (j : Nat) : Nat :=
  RT (Nat.add (nat_lit 109) (nth gl j))

@[expose] noncomputable def enumHeadK (RT ET : Nat → Nat) (D : TData) (e : Nat) : Bool :=
  (fun gl N => (fun K SR => bAnd(Nat.blt e (len (D.enums.map fun p => p.2)),
      bAnd(Nat.ble 1 N, bAnd(Nat.beq (keyAt K 0) key1, bAnd(Nat.blt (kf SR (Nat.sub N 1)) N,
      allBlk (nat_lit 0) (fun j => bAnd(Nat.blt (nth gl j) (nat_lit 109),
        bAnd(Nat.beq (pc (gT RT gl j) (gTI RT gl j)) pid,
          Nat.beq (pc (gTI RT gl j) (gT RT gl j)) pid))) (len gl))))))
      (ET (Nat.mul 4 e)) (ET (Nat.add (Nat.mul 4 e) 3)))
    (gensOf D e) (cardOf D e)

@[expose] noncomputable def enumPartK (RT ET : Nat → Nat) (D : TData) (e lo n : Nat) : Bool :=
  (fun gl N => (fun K PA LA SR => allBlk lo (fun i =>
      bAnd(Bool.rec (Bool.rec true (entK (gT RT gl) (len gl) K PA LA i) (Nat.blt i N)) true
          (Nat.beq i 0),
        bAnd(Bool.rec true (srtK N K SR i) (Nat.blt (Nat.succ i) N),
          Bool.rec true (cloK (gT RT gl) (len gl) N K SR i) (Nat.blt i N)))) n)
      (ET (Nat.mul 4 e)) (ET (Nat.add (Nat.mul 4 e) 1)) (ET (Nat.add (Nat.mul 4 e) 2))
      (ET (Nat.add (Nat.mul 4 e) 3)))
    (gensOf D e) (cardOf D e)

@[expose] noncomputable def prodAt (RT : Nat → Nat) (l : List Nat) (p : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) p (fun r _ ih => ap (RT r) ih) l

@[expose] noncomputable def regsLt (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun r _ ih => bAnd(Nat.blt r (nat_lit 109), ih)) l

@[expose] noncomputable def wordAt (PS PSI : Nat → Nat) (wd : List Nat) (p : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) p (fun a _ ih => ap (Bool.rec (PS (Nat.shiftRight a 1))
    (PSI (Nat.shiftRight a 1)) (Nat.beq (Nat.land a 1) 1)) ih) wd

@[expose] noncomputable def lettersLt (wd : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun a _ ih => bAnd(Nat.blt a (nat_lit 10), ih)) wd

@[expose] noncomputable def powAt (X j p : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) p (fun _ ih => ap X ih) j

@[expose] noncomputable def primeK (m : Nat) : Bool :=
  bAnd(Nat.ble 2 m, allBlk 2 (fun d => Bool.rec true false (Nat.beq (Nat.mod m d) 0))
    (Nat.sub m 2))

@[expose] noncomputable def memE (ET : Nat → Nat) (D : TData) (e t : Nat) : Bool :=
  bAnd(Nat.blt e (len (D.enums.map fun p => p.2)),
    memK (ET (Nat.mul 4 e)) (ET (Nat.add (Nat.mul 4 e) 3)) (cardOf D e) t)

@[expose] noncomputable def factK (RT ET PS PSI : Nat → Nat) (D : TData) (wd : List Nat) :
    TFact → Bool :=
  fun f => TFact.rec (motive := fun _ => Bool)
    (fun l₁ l₂ => bAnd(regsLt l₁, bAnd(regsLt l₂,
      Nat.beq (keyF (prodAt RT l₁)) (keyF (prodAt RT l₂)))))
    (fun l₁ l₂ => bAnd(regsLt l₁, bAnd(regsLt l₂,
      Bool.rec true false (Nat.beq (keyF (prodAt RT l₁)) (keyF (prodAt RT l₂))))))
    (fun e l => bAnd(regsLt l, memE ET D e (keyF (prodAt RT l))))
    (fun l => bAnd(regsLt l, bAnd(lettersLt wd,
      Nat.beq (keyF (prodAt RT l)) (keyF (wordAt PS PSI wd)))))
    (fun _ => false)
    (fun i m => bAnd(Nat.blt i (nat_lit 109), bAnd(primeK m,
      bAnd(Nat.beq (keyF (powAt (RT i) m)) key1,
        Bool.rec true false (Nat.beq (keyF (RT i |> ap)) key1))))) f

@[expose] noncomputable def isInP : TFact → Bool :=
  fun f => TFact.rec (motive := fun _ => Bool) (fun _ _ => false) (fun _ _ => false)
    (fun _ _ => false) (fun _ => true) (fun _ => false) (fun _ _ => false) f

@[expose] noncomputable def factsK (RT ET PS PSI : Nat → Nat) (D : TData) :
    List TFact → List (List Nat) → Bool :=
  fun l => List.rec (motive := fun _ => List (List Nat) → Bool) (fun _ => true)
    (fun f _ ih W => bAnd(factK RT ET PS PSI D (W.headD []) f,
      ih (Bool.rec W W.tail (isInP f)))) l

@[expose] noncomputable def condK (RT ET : Nat → Nat) (D : TData) (k : Nat) (fx fxi : Nat → Nat) :
    Cond → Bool :=
  fun c => Cond.rec (motive := fun _ => Bool)
    (fun r => bAnd(Nat.blt r (nat_lit 109),
      allB (fun b => Nat.beq (fx (ap (RT r) b)) (ap (RT r) (fx b)))))
    (fun w r => bAnd(Nat.blt w (nat_lit 109), bAnd(Nat.blt r (nat_lit 109),
      allB (fun b => Nat.beq (fx (ap (RT w) (ap (RT r) b))) (ap (RT r) (fx (ap (RT w) b)))))))
    (fun e r => bAnd(Nat.blt r (nat_lit 109),
      memE ET D e (keyF (fun b => fx (ap (RT r) (fxi b))))))
    (fun e => memE ET D e k)
    (fun _ ih => Bool.rec true false ih)
    (fun _ _ ih₁ ih₂ => bAnd(ih₁, ih₂))
    (fun _ _ ih₁ ih₂ => Bool.rec true ih₂ ih₁) c

@[expose] noncomputable def cntK (RT ET : Nat → Nat) (D : TData) (e : Nat) (c : Cond)
    (lo n : Nat) : Nat :=
  (fun gl => (fun K PA LA => Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun j ih => strictN ih (fun s => Nat.add s (Bool.rec (nat_lit 0) (nat_lit 1)
        (condK RT ET D (keyAt K (Nat.add lo j)) (atE (gT RT gl) PA LA (Nat.add lo j))
          (atIE (gTI RT gl) PA LA (Nat.add lo j)) c)))) n)
      (ET (Nat.mul 4 e)) (ET (Nat.add (Nat.mul 4 e) 1)) (ET (Nat.add (Nat.mul 4 e) 2)))
    (gensOf D e)

@[expose] noncomputable def loopK (RT ET : Nat → Nat) (D : TData) : TLoop → Bool :=
  fun l => TLoop.rec (motive := fun _ => Bool)
    (fun e c => bAnd(Nat.blt e (len (D.enums.map fun p => p.2)),
      Nat.beq (cntK RT ET D e c 0 (cardOf D e)) (cardOf D e)))
    (fun e c b => bAnd(Nat.blt e (len (D.enums.map fun p => p.2)),
      Nat.beq (cntK RT ET D e c 0 (cardOf D e)) b))
    (fun e c b => bAnd(Nat.blt e (len (D.enums.map fun p => p.2)),
      Nat.ble (cntK RT ET D e c 0 (cardOf D e)) b))
    (fun e c => bAnd(Nat.blt e (len (D.enums.map fun p => p.2)),
      Nat.blt 0 (cntK RT ET D e c 0 (cardOf D e)))) l

end CFSG.KC.J3Tk
