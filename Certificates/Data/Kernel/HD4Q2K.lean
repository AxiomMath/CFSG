module

public import Certificates.Data.Kernel.HTD42Q
public import Certificates.Data.HuppertD4Q2.Checker

public section

namespace CFSG.KC.HD4Q2K

open CFSG.KC.D4PlaneP CFSG.KC.HTD42Q HuppertD4Q2

abbrev Rec : Type := Nat × (Nat × Nat) × Bool × Nat × List (Nat × Nat)

@[expose] def oneQ : Nat × Nat := (oneP, 0)

@[expose] def atQ (L : List (Nat × Nat)) (i : Nat) : Nat × Nat := L.getD i oneQ

@[expose] noncomputable def memQ (x : Nat × Nat) (L : List (Nat × Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun a _ r => Bool.rec (motive := fun _ => Bool) r true (eqQ a x)) L

@[expose] noncomputable def nodupQ (L : List (Nat × Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun a l r => Bool.rec (motive := fun _ => Bool) false r (!memQ a l)) L

@[expose] noncomputable def eqLQ (L M : List (Nat × Nat)) : Bool :=
  List.rec (motive := fun _ => List (Nat × Nat) → Bool) (fun M => M.isEmpty)
    (fun a _ r M => List.rec (motive := fun _ => Bool) false
      (fun b M' _ => Bool.rec (motive := fun _ => Bool) false (r M') (eqQ a b)) M) L M

@[expose] noncomputable def gensQ (ls : List Nat) : List (Nat × Nat) :=
  [wordQ ls sWordA, wordQ ls sWordB, wordQ ls sWordC]

@[expose] noncomputable def enumQ (ls : List Nat) (es : List (Nat × Nat)) : Bool :=
  let G := gensQ ls
  Nat.beq es.length (sBfs.length + 1) && eqQ (atQ es 0) oneQ &&
    ((sBfs.zip es.tail).zipIdx.all fun q =>
      Nat.ble (q.1.1.1 + 1) (q.2 + 1) && eqQ q.1.2 (mulQ (atQ es q.1.1.1) (atQ G q.1.1.2)))

@[expose] noncomputable def powsQ (p : Nat × Nat) : List (Nat × Nat) := [oneQ, p, mulQ p p]

@[expose] noncomputable def planeQ9 (u v : Nat × Nat) : List (Nat × Nat) :=
  (powsQ u).flatMap fun a => (powsQ v).map fun b => mulQ a b

@[expose] noncomputable def sylowQ (ls : List Nat) (es : List (Nat × Nat)) : Bool :=
  let G := gensQ ls
  Nat.beq es.length 243 && nodupQ es && es.all fun x => G.all fun g => memQ (mulQ x g) es

@[expose] noncomputable def prsQ (es : List (Nat × Nat)) (prs : List (List (Nat × Nat))) : Bool :=
  Nat.beq prs.length planeRows.length &&
    (planeRows.zip prs).all fun q => eqLQ (planeQ9 (atQ es q.1.1) (atQ es q.1.2.1)) q.2

@[expose] noncomputable def isPairQ (x y : Nat × Nat) : Bool :=
  !eqQ x oneQ && cubeQ x && cubeQ y && eqQ (mulQ x y) (mulQ y x) && !memQ y (powsQ x)

@[expose] noncomputable def rowQ (ls : List Nat) (es : List (Nat × Nat)) (R1 R2 : List (Nat × Nat))
    (row : Nat × Nat × Nat × List Nat) (P : List (Nat × Nat)) : Bool :=
  let u := atQ es row.1
  let v := atQ es row.2.1
  let b := wordQ ls row.2.2.2
  let bi := wordQ ls (invW row.2.2.2)
  Nat.blt row.1 es.length && Nat.blt row.2.1 es.length && Nat.blt row.2.2.1 6 &&
    isPairQ u v && eqQ (mulQ b bi) oneQ &&
    memQ (mulQ (mulQ b (atQ R1 row.2.2.1)) bi) P && memQ (mulQ (mulQ b (atQ R2 row.2.2.1)) bi) P

@[expose] noncomputable def rowsQ (ls : List Nat) (es : List (Nat × Nat)) (prs : List (List (Nat × Nat)))
    (R1 R2 : List (Nat × Nat)) : Bool :=
  Nat.beq planeRows.length 121 && eqLQ (classR1.map (wordQ ls)) R1 && eqLQ (classR2.map (wordQ ls)) R2 &&
    (planeRows.zip prs).all fun q => rowQ ls es R1 R2 q.1 q.2

@[expose] noncomputable def recQ (es : List (Nat × Nat)) (prs : List (List (Nat × Nat))) (m : Rec) : Bool :=
  let x := m.2.1
  (m.2.2.1 == (cubeQ x && !eqQ x oneQ)) && Nat.blt m.2.2.2.1 243 && eqQ (atQ es m.2.2.2.1) (mulQ x x) &&
    m.2.2.2.2.all fun p => Nat.blt p.1 prs.length && eqQ (atQ (prs.getD p.1 []) p.2) x

@[expose] noncomputable def recsQ (es : List (Nat × Nat)) (prs : List (List (Nat × Nat))) (recs : List Rec) :
    Bool :=
  eqLQ (recs.map fun m => m.2.1) es && recs.zipIdx.all fun q => Nat.beq q.1.1 q.2 && recQ es prs q.1

@[expose] noncomputable def shareQ (pk pl : List (Nat × Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) false
    (fun a _ r => Bool.rec (motive := fun _ => Bool) r true
      (List.rec (motive := fun _ => Bool) false
        (fun b _ s => Bool.rec (motive := fun _ => Bool) s true (Nat.beq a.1 b.1)) pl)) pk

@[expose] noncomputable def pairQ (m n : Rec) : Bool :=
  Bool.rec (motive := fun _ => Bool) true
    (Bool.rec (motive := fun _ => Bool) true
      ((Nat.beq m.2.2.2.1 n.1 && Nat.beq n.2.2.2.1 m.1) || shareQ m.2.2.2.2 n.2.2.2.2)
      (eqQ (mulQ m.2.1 n.2.1) (mulQ n.2.1 m.2.1)))
    n.2.2.1

@[expose] noncomputable def coverQ (recs : List Rec) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun m rest r => Bool.rec (motive := fun _ => Bool) false r
      (Bool.rec (motive := fun _ => Bool) true
        (List.rec (motive := fun _ => Bool) true
          (fun n _ s => Bool.rec (motive := fun _ => Bool) false s (pairQ m n)) rest)
        m.2.2.1)) recs

@[expose] noncomputable def centerQ (ls : List Nat) (es : List (Nat × Nat)) : Bool :=
  let G := gensQ ls
  let C := es.filter fun z => G.all fun g => eqQ (mulQ z g) (mulQ g z)
  Nat.beq C.length 3 && C.all fun z => Nat.beq z.2 0

@[expose] noncomputable def slpQ (gens invs : List (Nat × Nat)) (ids : List Nat) : Nat × Nat :=
  ids.foldl (fun acc i => mulQ acc (if i % 2 = 0 then atQ gens (i / 2) else atQ invs (i / 2))) oneQ

@[expose] noncomputable def classQ (ls : List Nat) (cg ci : List (List (Nat × Nat))) (i : Nat) : Bool :=
  let r1 := wordQ ls (classR1.getD i [])
  let r2 := wordQ ls (classR2.getD i [])
  let w1 := classG1.getD i []
  let w2 := classG2.getD i []
  let gens := cg.getD i []
  let invs := ci.getD i []
  let slps := classSlp.getD i []
  eqLQ ((w1 ++ w2).map (wordQ ls)) gens && eqLQ ((w1 ++ w2).map fun w => wordQ ls (invW w)) invs &&
    !eqQ r1 oneQ && !eqQ r2 oneQ &&
    (w1 ++ w2).all (fun w => Nat.beq (wordQ ls w).2 0) &&
    (gens.take w1.length).all (fun s => eqQ (mulQ r1 s) (mulQ s r1)) &&
    (gens.drop w1.length).all (fun s => eqQ (mulQ r2 s) (mulQ s r2)) &&
    (gens.zip invs).all (fun q => eqQ (mulQ q.1 q.2) oneQ) &&
    slps.all (fun x => Nat.blt x.1 18 && eqQ (slpQ gens invs x.2) (letP ls x.1, 0)) &&
    (List.range 18).all fun k => slps.any fun x => Nat.beq x.1 k

end CFSG.KC.HD4Q2K
