module

public import Certificates.Data.Kernel.Misc.G24

public section

namespace CFSG.KC.A9Mod

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc CFSG.KC.Misc.G24

abbrev SpinRec : Type :=
  List (Nat × Bool) × (List (Nat × (Nat × Nat)) × (List (Nat × Nat) × Nat))

abbrev WitRec : Type := Nat × (Nat × (Nat × Nat))

abbrev SubRec : Type := Nat × (SpinRec × List WitRec)

abbrev NodeRec : Type := Nat × (SpinRec × List SubRec)

abbrev S1Rec : Type := Nat × (Nat × (Nat × Nat))

@[expose] noncomputable def mulQ (a b : Nat) : Nat := mulF2 8 b a

@[expose] noncomputable def IDQ : Nat := 9241421688590303745

@[expose] noncomputable def mvQ (a v : Nat) : Nat := Nat.land (mulQ a (Nat.land v 255)) 255

@[expose] noncomputable def powQ (q k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) IDQ (fun _ ih => mulQ ih q) k

@[expose] noncomputable def packMap {α : Type} (f : α → Nat) (cs : List α) : Nat :=
  List.rec (motive := fun _ => Nat) 0
    (fun c _ ih => Nat.lor (Nat.land (f c) 255) (Nat.shiftLeft ih 8)) cs

@[expose] noncomputable def getN (l : List Nat) (i : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun x _ ih i => Nat.rec (motive := fun _ => Nat) x (fun k _ => ih k) i) l i

@[expose] noncomputable def getX (gens : List (Nat × Bool)) (i : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun g _ ih i => Nat.rec (motive := fun _ => Nat) (Prod.rec (motive := fun _ => Nat)
      (fun x _ => x) g) (fun k _ => ih k) i) gens i

@[expose] noncomputable def sel4 (x0 x1 x2 x3 i : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (Bool.rec (motive := fun _ => Nat) x3 x2 (Nat.beq i 2))
    (Bool.rec (motive := fun _ => Nat) x1 x0 (Nat.beq i 0)) (Nat.blt i 2)

@[expose] noncomputable def sel8 (a0 a1 a2 a3 b0 b1 b2 b3 i : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (sel4 b0 b1 b2 b3 (Nat.sub i 4)) (sel4 a0 a1 a2 a3 i)
    (Nat.blt i 4)

@[expose] noncomputable def evalFrom (a0 a1 a2 a3 b0 b1 b2 b3 : Nat) (w : List Nat) :
    Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun r => r)
    (fun i _ ih r => ih (mulQ r (sel8 a0 a1 a2 a3 b0 b1 b2 b3 i))) w

@[expose] noncomputable def evalWQ (a0 a1 a2 a3 b0 b1 b2 b3 : Nat) (w : List Nat) : Nat :=
  evalFrom a0 a1 a2 a3 b0 b1 b2 b3 w IDQ

@[expose] noncomputable def relsQ (g s1 s2 s3 : Nat) (rels : List (List Nat)) : Bool :=
  letB (powQ g 8) fun gi => letB (powQ s1 5) fun s1i => letB (powQ s3 2) fun s3i =>
    List.rec (motive := fun _ => Bool) true
      (fun r _ ih => andB (Nat.beq (evalWQ g s1 s2 s3 gi s1i s2 s3i r) IDQ) ih) rels

@[expose] noncomputable def allP {α : Type} (l : List α) (f : α → Bool) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun c _ ih => andB (f c) ih) l

@[expose] noncomputable def allV (P : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun v ih => andB (P v) ih) 256

@[expose] noncomputable def colsOK (A' : Nat → Nat) (cs : List (Nat × (Nat × Nat))) : Bool :=
  allP cs fun c => Prod.rec (motive := fun _ => Bool)
    (fun j p => Prod.rec (motive := fun _ => Bool) (fun M _ => Nat.beq (A' j) M) p) c

@[expose] noncomputable def fixOK (A A' : Nat → Nat) (gens : List (Nat × Bool))
    (fs : List (Nat × Nat)) : Bool :=
  allP fs fun e => Prod.rec (motive := fun _ => Bool) (fun j M => andB (Nat.beq (A' j) M)
    (allP gens fun g => Prod.rec (motive := fun _ => Bool) (fun x fx =>
      Bool.rec (motive := fun _ => Bool) true (Nat.beq (mvQ (A j) x) (Nat.land x 255)) fx) g)) e

@[expose] noncomputable def wQ (A : Nat → Nat) (gens : List (Nat × Bool))
    (cs : List (Nat × (Nat × Nat))) : Nat :=
  packMap (fun c => Prod.rec (motive := fun _ => Nat) (fun j p => Prod.rec (motive := fun _ => Nat)
    (fun _ i => mvQ (A j) (getX gens i)) p) c) cs

@[expose] noncomputable def dQ (cs : List (Nat × (Nat × Nat))) (vals : List Nat) : Nat :=
  packMap (fun c => Prod.rec (motive := fun _ => Nat) (fun _ p => Prod.rec (motive := fun _ => Nat)
    (fun M i => mvQ M (getN vals i)) p) c) cs

@[expose] noncomputable def fixV (fs : List (Nat × Nat)) (v : Nat) : Bool :=
  allP fs fun e => Prod.rec (motive := fun _ => Bool) (fun _ M => Nat.beq (mvQ M v) v) e

@[expose] noncomputable def enumG (fs : List (Nat × Nat)) (gens : List (Nat × Bool)) :
    (List Nat → Bool) → Bool :=
  List.rec (motive := fun _ => (List Nat → Bool) → Bool) (fun k => k [])
    (fun g _ ih k => Prod.rec (motive := fun _ => Bool) (fun _ fx => allV fun v =>
      orB (andB fx (notB (fixV fs v))) (ih fun vs => k (List.cons v vs))) g) gens

@[expose] noncomputable def spinOK (A A' : Nat → Nat) (r : SpinRec) (leaf : Nat → Bool) : Bool :=
  Prod.rec (motive := fun _ => Bool) (fun gens r2 => Prod.rec (motive := fun _ => Bool)
    (fun cs r3 => Prod.rec (motive := fun _ => Bool) (fun fs Winv =>
      andB (colsOK A' cs) (andB (fixOK A A' gens fs) (andB (Nat.beq (mulQ (wQ A gens cs) Winv) IDQ)
        (enumG fs gens fun vals => leaf (mulQ (dQ cs vals) Winv))))) r3) r2) r

@[expose] noncomputable def relsK1Q : List (List Nat) :=
  [[1, 4, 5, 0, 0],
    [1, 1, 1, 1, 1, 1],
    [1, 1, 4, 4, 5, 5, 4]]

@[expose] noncomputable def relsK2Q : List (List Nat) :=
  [[2, 2],
    [4, 1, 0, 5, 4],
    [4, 1, 1, 4, 2, 4, 4, 2],
    [4, 2, 0, 0, 5, 0, 5, 0, 2],
    [0, 5, 0, 2, 1, 0, 2, 0, 5, 2]]

@[expose] noncomputable def relsA9Q : List (List Nat) :=
  [[2, 2],
    [3, 3, 3],
    [1, 0, 5, 4, 4],
    [1, 4, 1, 2, 0, 2],
    [5, 5, 2, 1, 1, 2],
    [5, 0, 1, 1, 0, 0, 5],
    [3, 5, 0, 3, 4, 2, 4, 2],
    [2, 4, 4, 4, 2, 4, 4, 4],
    [0, 5, 0, 2, 0, 5, 0, 2, 0, 5, 0, 2],
    [0, 0, 2, 1, 0, 2, 7, 4, 2, 4, 1, 2, 3],
    [2, 4, 4, 4, 4, 3, 2, 7, 2, 0, 1, 0, 2, 5, 2, 0, 3, 5, 3, 2, 0, 0, 3],
    [3, 4, 3, 5, 3, 2, 0, 0, 3, 4, 3, 4, 3, 1, 7, 2, 0, 7, 5, 3, 1, 3, 2],
    [7, 0, 7, 4, 4, 2, 7, 1, 7, 0, 3, 2, 7, 0, 7, 4, 4, 2, 7, 1, 7, 0, 3, 2],
    [0, 2, 5, 0, 3, 1, 7, 2, 0, 7, 5, 3, 1, 0, 2, 5, 0, 3, 1, 7, 2, 0, 7, 5, 3, 1],
    [1, 4, 2, 7, 4, 4, 2, 7, 1, 7, 0, 2, 7, 2, 4, 3, 5, 3, 2, 0, 0, 3, 2, 0, 5, 3],
    [7, 1, 4, 1, 4, 1, 7, 4, 3, 5, 3, 2, 0, 0, 3, 4, 7, 2, 7, 2, 4, 5, 4, 5, 5, 3, 2],
    [7, 2, 3, 2, 5, 7, 1, 3, 2, 0, 7, 4, 7, 0, 3, 2, 7, 5, 4, 5, 3, 2, 7, 2, 4, 1, 3, 2, 3, 2],
    [5, 7, 1, 3, 2, 0, 7, 4, 7, 0, 5, 7, 1, 3, 2, 0, 7, 4, 7, 0, 5, 7, 1, 3, 2, 0, 7, 4, 7, 0],
    [3, 1, 4, 2, 7, 4, 4, 2, 7, 1, 7, 0, 7, 2, 5, 7, 1, 3, 2, 0, 7, 4, 7, 0, 2, 3, 2, 7, 2, 4, 3,
      5, 3, 2, 0, 0, 3, 4],
    [5, 7, 1, 3, 2, 0, 7, 4, 7, 0, 2, 3, 2, 7, 2, 3, 2, 7, 2, 3, 2, 7, 4, 2, 4, 7, 1, 3, 2, 0, 7,
      4, 7, 0, 3, 2, 7, 2],
    [5, 7, 1, 3, 2, 0, 7, 4, 7, 5, 4, 5, 5, 3, 2, 7, 2, 4, 3, 5, 3, 2, 0, 0, 3, 4, 4, 3, 1, 7, 2,
      0, 7, 5, 3, 1, 0, 7, 4, 4, 2, 7, 1, 7, 0, 2],
    [1, 3, 2, 7, 2, 0, 1, 7, 4, 4, 2, 7, 1, 7, 0, 2, 3, 1, 4, 2, 4, 7, 4, 3, 1, 7, 2, 0, 7, 5, 3,
      1, 2, 4, 3, 5, 3, 2, 0, 0, 3, 4, 3, 2, 7, 2, 4]]

@[expose] noncomputable def wordHQ : List Nat := [0, 1, 1, 0, 1, 1]

@[expose] noncomputable def wordsLQ : List (List Nat × List Nat) :=
  [([], []),
   ([0, 2, 1, 2, 0], [0, 2, 1, 2, 0]),
   ([2, 1, 0, 1], [2, 1, 0, 1]),
   ([0, 1, 0, 0, 0, 2], [0, 1, 0, 0, 0, 2]),
   ([0, 2, 1, 0], [0, 2, 1, 0]),
   ([1, 0, 1, 1], [1, 0, 1, 1]),
   ([0, 0, 0], [0, 1, 2]),
   ([1, 1, 2, 1, 2], [0, 0, 2, 0]),
   ([0, 0, 2, 0], [0, 1, 1, 0, 1]),
   ([0, 1, 2], [1, 1, 0, 0, 2, 1]),
   ([1, 1, 0, 0, 2, 1], [0, 0, 0]),
   ([0, 1, 1, 0, 1], [1, 1, 2, 1, 2]),
   ([2, 0, 0, 0, 2], [1, 0, 1, 2, 1]),
   ([1, 0, 2, 0, 1], [1, 1, 1, 0]),
   ([2, 0, 1, 1, 0], [1, 0, 2, 0, 1]),
   ([1, 0, 0, 2], [2, 0, 0, 0, 2]),
   ([1, 0, 1, 2, 1], [1, 0, 0, 2]),
   ([1, 1, 1, 0], [2, 0, 1, 1, 0])]

@[expose] noncomputable def wordAQ : List Nat := [1, 1, 3, 2, 3, 2, 0, 3, 0, 3, 0]

@[expose] noncomputable def wordBQ : List Nat := [3, 0, 0, 2, 3, 0, 3, 1, 3, 3, 2]

@[expose] noncomputable def wordB'Q : List Nat := [0, 1, 1, 3, 2, 1, 3, 1, 3, 2, 1, 3, 1]

@[expose] noncomputable def N1Q : Nat := 13871096885613691906

@[expose] noncomputable def N2Q : Nat := 9241396468676822018

@[expose] noncomputable def B1MQ : Nat := 2310487621274960130

@[expose] noncomputable def B2MQ : Nat := 17893373086493939202

@[expose] noncomputable def P8AQ : Nat := 4647732545138983170

@[expose] noncomputable def P8BQ : Nat := 13880239773630759041

@[expose] noncomputable def getL (j : Nat) : List Nat × List Nat :=
  List.rec (motive := fun _ => Nat → List Nat × List Nat) (fun _ => ([], []))
    (fun x _ ih i => Nat.rec (motive := fun _ => List Nat × List Nat) x (fun k _ => ih k) i)
    wordsLQ j

@[expose] noncomputable def s1Match (N : Nat) (recs : List S1Rec) (reps : List Nat) (m : Nat) :
    Bool :=
  List.rec (motive := fun _ => Bool) false (fun e _ ih => Prod.rec (motive := fun _ => Bool)
    (fun m1 e2 => Bool.rec (motive := fun _ => Bool) ih (Prod.rec (motive := fun _ => Bool)
      (fun C e3 => Prod.rec (motive := fun _ => Bool) (fun Ci R =>
        andB (Nat.beq (mulQ C N) (mulQ N C)) (andB (Nat.beq (mulQ C Ci) IDQ)
          (andB (Nat.beq (mulQ Ci C) IDQ) (andB (Nat.beq (mulQ C m1) (mulQ R C))
            (memN R reps))))) e3) e2) (Nat.beq m m1)) e) recs

@[expose] noncomputable def s1OK (N : Nat) (sr : SpinRec) (recs : List S1Rec) (reps : List Nat) :
    Bool :=
  letB (mulQ N N) fun N2 => spinOK (powQ N) (powQ N2) sr fun m =>
    orB (notB (relsQ N m IDQ IDQ relsK1Q)) (s1Match N recs reps m)

@[expose] noncomputable def conjQ (N R m2 m3 t P Pi : Nat) : Bool :=
  letB (powQ N 8) fun gi => letB (powQ R 5) fun ri => letB (powQ m3 2) fun ti =>
  letB (evalWQ N R m2 m3 gi ri m2 ti wordAQ) fun ra =>
  letB (evalWQ N R m2 m3 gi ri m2 ti
    (Bool.rec (motive := fun _ => List Nat) wordBQ wordB'Q (Nat.beq t 1))) fun rb =>
  andB (Nat.beq (mulQ P ra) (mulQ (Bool.rec (motive := fun _ => Nat) B1MQ P8AQ (Nat.beq t 2)) P))
    (andB (Nat.beq (mulQ P rb) (mulQ (Bool.rec (motive := fun _ => Nat) B2MQ P8BQ (Nat.beq t 2)) P))
      (Nat.beq (mulQ Pi P) IDQ))

@[expose] noncomputable def witMatch (N R m2 : Nat) (wits : List WitRec) (m : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun e _ ih => Prod.rec (motive := fun _ => Bool)
    (fun m3 e2 => Bool.rec (motive := fun _ => Bool) ih (Prod.rec (motive := fun _ => Bool)
      (fun t e3 => Prod.rec (motive := fun _ => Bool) (fun P Pi => conjQ N R m2 m3 t P Pi) e3) e2)
      (Nat.beq m m3)) e) wits

@[expose] noncomputable def s3OK (N R m2 : Nat) (sr : SpinRec) (wits : List WitRec) : Bool :=
  letB (powQ N 8) fun gi => letB (powQ R 5) fun ri =>
  spinOK (fun j => evalWQ N R m2 IDQ gi ri m2 IDQ (Prod.rec (motive := fun _ => List Nat)
      (fun w _ => w) (getL j)))
    (fun j => evalWQ N R m2 IDQ gi ri m2 IDQ (Prod.rec (motive := fun _ => List Nat)
      (fun _ w => w) (getL j))) sr fun m =>
    orB (notB (relsQ N R m2 m relsA9Q)) (witMatch N R m2 wits m)

@[expose] noncomputable def memS (subs : List SubRec) (m : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun e _ ih => orB (Prod.rec (motive := fun _ => Bool)
    (fun m2 _ => Nat.beq m m2) e) ih) subs

@[expose] noncomputable def nodeOK (N : Nat) (nd : NodeRec) : Bool :=
  Prod.rec (motive := fun _ => Bool) (fun R e2 => Prod.rec (motive := fun _ => Bool) (fun sr subs =>
    letB (evalWQ N R IDQ IDQ (powQ N 8) (powQ R 5) IDQ IDQ wordHQ) fun H =>
    andB (spinOK (powQ N) (powQ H) sr fun m =>
        orB (notB (relsQ N R m IDQ relsK2Q)) (memS subs m))
      (allP subs fun e => Prod.rec (motive := fun _ => Bool) (fun m2 e3 =>
        Prod.rec (motive := fun _ => Bool) (fun sr3 wits => s3OK N R m2 sr3 wits) e3) e)) e2) nd

@[expose] noncomputable def repsOf {β : Type} (nodes : List (Nat × β)) : List Nat :=
  List.rec (motive := fun _ => List Nat) []
    (fun e _ ih => List.cons (Prod.rec (motive := fun _ => Nat) (fun R _ => R) e) ih) nodes

end CFSG.KC.A9Mod
