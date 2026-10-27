module

public import Certificates.Data.Kernel.LocalQT.CovT

public section

namespace CFSG.KC.LQT.Cov

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.LQT.S CFSG.KC.LQT.W CFSG.KC.LQT.T2 CFSG.KC.LQT.Syl
open CFSG.KS CFSG.KC.Enum

structure CH where
  xw : List (List Nat)
  nV : Nat
  words : List (List Nat)
  tgt : List Nat
  back : List Nat
  pairs : List (List Nat × Nat × Nat)
  anchors : List (List Nat × Nat)

@[expose] noncomputable def pairsH (L : List (List Char)) (np pos : Nat) :
    Option (List (List Nat × Nat × Nat) × Nat) :=
  Nat.rec (motive := fun _ => Nat → Option (List (List Nat × Nat × Nat) × Nat))
    (fun p => some ([], p))
    (fun _ ih p =>
      Option.rec (motive := fun _ => Option _) none (fun gw =>
      Option.rec (motive := fun _ => Option _) none (fun ab =>
      Option.rec (motive := fun _ => Option _) none (fun rest =>
        Bool.rec (motive := fun _ => Option _) none
          (some (List.cons (gw, getK ab 0 0, getK ab 1 0) rest.1, rest.2))
          (Nat.beq (lenK ab) 2))
        (ih (Nat.add p 2)))
        (natsK (getK L (Nat.add p 1) [])))
        (natsK (getK L p []))) np pos

@[expose] noncomputable def anchorsH (L : List (List Char)) (na pos : Nat) :
    Option (List (List Nat × Nat)) :=
  Nat.rec (motive := fun _ => Nat → Option (List (List Nat × Nat)))
    (fun _ => some [])
    (fun _ ih p =>
      Option.rec (motive := fun _ => Option _) none (fun gw =>
      Option.rec (motive := fun _ => Option _) none (fun b =>
      Option.rec (motive := fun _ => Option _) none (fun rest =>
        some (List.cons (gw, b) rest))
        (ih (Nat.add p 2)))
        (natK (getK L (Nat.add p 1) [])))
        (natsK (getK L p []))) na pos

@[expose] noncomputable def parseH (cs : List Char) : Option CH :=
  Option.rec (motive := fun _ => Option CH) none (fun xw =>
  Option.rec (motive := fun _ => Option CH) none (fun nV =>
  Option.rec (motive := fun _ => Option CH) none (fun words =>
  Option.rec (motive := fun _ => Option CH) none (fun tgt =>
  Option.rec (motive := fun _ => Option CH) none (fun back =>
  Option.rec (motive := fun _ => Option CH) none (fun np =>
  Option.rec (motive := fun _ => Option CH) none (fun pr =>
  Option.rec (motive := fun _ => Option CH) none (fun na =>
  Option.rec (motive := fun _ => Option CH) none (fun an =>
    some ⟨xw, nV, words, tgt, back, pr.1, an⟩)
    (anchorsH (linesK cs) na (Nat.succ pr.2)))
    (natK (getK (linesK cs) pr.2 [])))
    (pairsH (linesK cs) np (Nat.add 7 nV)))
    (natK (getK (linesK cs) (Nat.add 6 nV) [])))
    (natsK (getK (linesK cs) (Nat.add 5 nV) [])))
    (natsK (getK (linesK cs) (Nat.add 4 nV) [])))
    (manyK (linesK cs) wordK 4 nV))
    (natK (getK (linesK cs) 3 [])))
    (manyK (linesK cs) natsK 0 3)

@[expose] noncomputable def wPK (n w A B : Nat) (wd : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun l _ ih acc => strictN (pcomp n w (mask w) acc
      (Bool.rec (motive := fun _ => Nat) B A (Nat.beq l 0))) ih) wd (pidn n w)

@[expose] noncomputable def buildEH (n w : Nat) (X : List Nat) (WR : List (List (List Nat)))
    (P : List Nat) (k : List Nat → Bool) : Bool :=
  List.rec (motive := fun _ => Nat → List Nat → Bool)
    (fun _ acc => List.rec (motive := fun _ => List Nat → Bool) (fun r => k r)
      (fun x _ ih r => ih (List.cons x r)) acc [])
    (fun p _ ih c acc => strictB c fun c =>
      strictB (pcomp n w (mask w) (getK acc (Nat.sub (Nat.sub c 1) p) 0)
        (getK X (Nat.mod (lastK (getRG WR c [])) 3) 0)) fun e =>
      ih (Nat.succ c) (List.cons e acc))
    P 1 [pidn n w]

@[expose] noncomputable def goodH (d : CH) (WR : List (List (List Nat))) (TG TB PR : List (List Nat))
    (n w : Nat) (X : List Nat) (ER : List (List Nat)) : Bool :=
  allBs [Nat.blt 0 d.nV, Nat.beq (lenK (getK d.words 0 [1])) 0,
    allLtK d.nV (fun v => allLtK 3 fun i =>
      strictB (getRG TG (Nat.add (Nat.mul 3 v) i) d.nV) fun t =>
      allBs [Nat.blt t d.nV,
        Nat.blt (getRG TB (Nat.add (Nat.mul 3 v) i) d.nV) d.nV,
        Bool.rec (motive := fun _ => Bool)
          (Nat.beq (getRG ER t 0) (pcomp n w (mask w) (getRG ER v 0) (getK X i 0))) true
          (andB (notB (Nat.beq t 0)) (andB (Nat.beq (getRG PR (Nat.sub t 1) 0) v)
            (Nat.beq (Nat.mod (lastK (getRG WR t [])) 3) i))),
        Nat.beq (getRG TG (Nat.add (Nat.mul 3 (getRG TB (Nat.add (Nat.mul 3 v) i) 0)) i) 0) v])]

@[expose] noncomputable def pairH (n w A B : Nat) (d : CH) (ER : List (List Nat))
    (r : List Nat × Nat × Nat) : Bool :=
  strictB (wPK n w A B r.1) fun Ga =>
  strictB (pinvS n w (mask w) Ga) fun Gi =>
  allBs [permOK n w (mask w) (Nat.mul n w) Ga Gi, Nat.blt r.2.1 d.nV, Nat.blt r.2.2 d.nV,
    Nat.beq (pcomp n w (mask w) (pcomp n w (mask w) Gi (getRG ER r.2.1 0)) Ga)
      (getRG ER r.2.2 0)]

@[expose] noncomputable def anchorH (n w A B C : Nat) (d : CH) (ER : List (List Nat))
    (r : List Nat × Nat) : Bool :=
  strictB (wPK n w A B r.1) fun Ga =>
  strictB (pinvS n w (mask w) Ga) fun Gi =>
  allBs [permOK n w (mask w) (Nat.mul n w) Ga Gi, Nat.blt r.2 d.nV,
    Nat.beq (pcomp n w (mask w) (pcomp n w (mask w) Gi C) Ga) (getRG ER r.2 0)]

@[expose] noncomputable def stepH (TG TB : List (List Nat)) (v : Nat) (l : Nat × Bool) : Nat :=
  Bool.rec (motive := fun _ => Nat) (getRG TB (Nat.add (Nat.mul 3 v) l.1) 0)
    (getRG TG (Nat.add (Nat.mul 3 v) l.1) 0) l.2

@[expose] noncomputable def edgeH (TB : List (List Nat)) (v : Nat) (l : Nat × Bool) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (Nat.add (Nat.mul 3 (getRG TB (Nat.add (Nat.mul 3 v) l.1) 0)) l.1)
    (Nat.add (Nat.mul 3 v) l.1) l.2

@[expose] noncomputable def walkH (TG TB : List (List Nat)) (v : Nat) (w : List (Nat × Bool)) :
    Nat × Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat × Nat) (fun f v => (f, v))
    (fun l _ ih f v => letNN (Nat.xor f (Nat.pow 2 (edgeH TB v l))) fun f' =>
      letNN (stepH TG TB v l) fun v' => ih f' v') w 0 v

@[expose] noncomputable def sqH (WR : List (List (List Nat))) (TG TB : List (List Nat)) (v : Nat) :
    Nat × Nat :=
  walkH TG TB v (posK (getRG WR v []))

@[expose] noncomputable def eqnsH (d : CH) (WR : List (List (List Nat))) (TG TB : List (List Nat)) :
    List (Bool × Nat) :=
  letI edges := List.flatten (List.map (fun v => List.map (fun i => (v, i)) [0, 1, 2])
    (List.range d.nV))
  letI isT := fun (p : Nat × Nat) =>
    eqL (getRG WR (getRG TG (Nat.add (Nat.mul 3 p.1) p.2) 0) [])
      (List.append (getRG WR p.1 []) [p.2])
  List.append (List.append (List.append
    (List.map (fun p => (Nat.blt p.1 d.nV, Nat.pow 2 (Nat.add (Nat.mul 3 p.1) p.2)))
      (List.filter isT edges))
    (List.flatten (List.map (fun p =>
      letI w := List.append (List.append (posK (getRG WR p.1 [])) [(p.2, true)])
        (invWK (getRG WR (getRG TG (Nat.add (Nat.mul 3 p.1) p.2) 0) []))
      List.map (fun j =>
        letI r0 := walkH TG TB 0 w
        letI r1 := walkH TG TB (getRG TG j 0) w
        (allBs [Nat.blt (getRG TG j 0) d.nV, Nat.beq r0.2 0, Nat.beq r1.2 (getRG TG j 0)],
          Nat.xor r0.1 r1.1)) [0, 1, 2])
      (List.filter (fun p => notB (isT p)) edges))))
    (List.map (fun r =>
      letI ra := sqH WR TG TB r.2.1
      letI rb := sqH WR TG TB r.2.2
      (allBs [Nat.blt r.2.1 d.nV, Nat.blt r.2.2 d.nV, Nat.beq ra.2 0, Nat.beq rb.2 0],
        Nat.xor ra.1 rb.1)) d.pairs))
    (List.map (fun r =>
      letI rb := sqH WR TG TB r.2
      (andB (Nat.blt r.2 d.nV) (Nat.beq rb.2 0), rb.1)) d.anchors)

@[expose] noncomputable def covHA (n w A B : Nat) (cs : List Char) (P : List Nat) (nV0 : Nat) :
    Bool :=
  Option.rec (motive := fun _ => Bool) false (fun d =>
    letI WR := rowsG d.words
    letI X := List.map (wPK n w A B) d.xw
    allBs [CFSG.KS.Raw.szOK n w, Nat.beq (lenK d.xw) 3, Nat.beq d.nV nV0,
      permOK n w (mask w) (Nat.mul n w) A (pinvS n w (mask w) A),
      permOK n w (mask w) (Nat.mul n w) B (pinvS n w (mask w) B),
      parOK WR d.nV P,
      strictB (wPK n w A B [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1]) fun C =>
      buildEH n w X WR P fun E =>
        letI ER := rowsG E
        allBs [goodH d WR (rowsG d.tgt) (rowsG d.back) (rowsG P) n w X ER, distinctS E,
          allT d.pairs (pairH n w A B d ER), allT d.anchors (anchorH n w A B C d ER)]])
    (parseH cs)

@[expose] noncomputable def covHB (cs : List Char) (H : List (List Nat)) : Bool :=
  Option.rec (motive := fun _ => Bool) false (fun d =>
    letI Q := eqnsH d (rowsG d.words) (rowsG d.tgt) (rowsG d.back)
    letI F := List.map (fun q => q.2) Q
    allBs [Nat.beq (lenK H) (Nat.mul 3 d.nV), triT (rowsG F) H,
      List.rec (motive := fun _ => Bool) true (fun q _ ih => andB q.1 ih) Q,
      allL F (fun f => Nat.blt f (Nat.pow 2 (Nat.mul 3 d.nV)))])
    (parseH cs)

end CFSG.KC.LQT.Cov

end
