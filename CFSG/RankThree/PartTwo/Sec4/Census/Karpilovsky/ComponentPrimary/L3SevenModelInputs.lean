module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.L3SevenData
public import CFSG.RankThree.Native.ONTripleModelInputs

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.L3Seven

open CFSG.RankThree.Native.ONTriple CFSG.KC.Misc.F7 CFSG.KC.Loop

@[expose] def rRegL (j l : ℕ) : ℕ := (rL.getD j []).getD l 0

@[expose] def rRegV (j m i : ℕ) : ℕ := ((rV.getD j []).getD m []).getD i 0

@[expose] def lRows : List (List (List ℕ)) :=
  [[[0, 0, 0, 1], [0, 1, 2, 2], [0, 2, 1, 0], [1, 0, 2, 0], [1, 1, 1, 1], [1, 2, 0, 2],
      [2, 0, 1, 2], [2, 1, 0, 0], [2, 2, 2, 1]],
    [[0, 0, 0, 1], [0, 1, 2, 2], [0, 2, 1, 0], [1, 0, 1, 2], [1, 1, 0, 0], [1, 2, 2, 1],
      [2, 0, 2, 0], [2, 1, 1, 1], [2, 2, 0, 2]]]

@[expose] def rowAt (j k l : ℕ) : ℕ := ((lRows.getD j []).getD k []).getD l 0

@[expose] def sel4 {α : Type _} (a b c d : α) : ℕ → α
  | 0 => a
  | 1 => b
  | 2 => c
  | _ => d

@[expose] noncomputable def xC (j l m i : ℕ) : ℕ :=
  mmul (mmul (rIM (rRegL j l)) (rM (rRegV j m i))) (rM (rRegL j l))

@[expose] noncomputable def xIdx (j q : ℕ) : ℕ := xC j (q / 9) (q / 3 % 3) (q % 3)

@[expose] noncomputable def selJ {α : Type} (j : ℕ) (a b : α) : α :=
  Bool.rec (motive := fun _ => α) b a (Nat.beq j 0)

@[expose] noncomputable def splitW (l : List ℕ) : List (List (ℕ × Bool)) :=
  (List.rec (motive := fun _ => List (ℕ × Bool) × List (List (ℕ × Bool))) (List.nil, List.nil)
    (fun c _ ih => Nat.rec (motive := fun _ => List (ℕ × Bool) × List (List (ℕ × Bool)))
      (List.nil, List.cons ih.1 ih.2)
      (fun c' _ => (List.cons (Nat.div c' 2, Nat.beq (Nat.mod c' 2) 1) ih.1, ih.2)) c) l).2

@[expose] noncomputable def nthWd (l : List (List (ℕ × Bool))) (i : ℕ) : List (ℕ × Bool) :=
  List.rec (motive := fun _ => ℕ → List (ℕ × Bool)) (fun _ => List.nil)
    (fun x _ ih j => Nat.rec (motive := fun _ => List (ℕ × Bool)) x (fun j' _ => ih j') j) l i

@[expose] noncomputable def invW (w : List (ℕ × Bool)) : List (ℕ × Bool) :=
  List.rec (motive := fun _ => List (ℕ × Bool) → List (ℕ × Bool)) (fun acc => acc)
    (fun l _ ih acc => ih (List.cons (l.1, notB l.2) acc)) w List.nil

@[expose] noncomputable def snocN (F : List ℕ) (v : ℕ) : List ℕ :=
  List.rec (motive := fun _ => List ℕ) (List.cons v List.nil) (fun x _ ih => List.cons x ih) F

@[expose] noncomputable def buildL (n : ℕ) (f : ℕ → ℕ) (k : List ℕ → Bool) : Bool :=
  Nat.rec (motive := fun _ => List ℕ → Bool) (fun acc => k acc)
    (fun i ih acc => strictB (f i) fun v => ih (List.cons v acc)) n List.nil

@[expose] noncomputable def runK (prog : List (List (ℕ × Bool))) (F FI : List ℕ)
    (k : List ℕ → List ℕ → Bool) : Bool :=
  List.rec (motive := fun _ => List ℕ → List ℕ → Bool) (fun F FI => k F FI)
    (fun w _ ih F FI => strictB (wordC (nthN F) (nthN FI) w) fun v =>
      strictB (wordC (nthN F) (nthN FI) (invW w)) fun vi => ih (snocN F v) (snocN FI vi))
    prog F FI

@[expose] noncomputable def symWd (j s : ℕ) : List (ℕ × Bool) :=
  nthWd (splitW dSymW) (Nat.add (Nat.mul 2 j) s)

@[expose] noncomputable def piAt (j s q : ℕ) : ℕ :=
  nthN dSymPi (Nat.add (Nat.mul 24 (Nat.add (Nat.mul 2 j) s)) q)

@[expose] noncomputable def symOK (xs : List ℕ) (j s : ℕ) : Bool :=
  strictB (wordC rM rIM (symWd j s)) fun T => strictB (wordC rM rIM (invW (symWd j s))) fun TI =>
    allN 24 fun q => Nat.beq (mmul (mmul TI (nthN xs (3 * (q / 2) + q % 2))) T)
      (nthN xs (piAt j s q))

@[noinline, expose] noncomputable def chkSymM (j : ℕ) : Bool :=
  buildL 36 (xIdx j) fun xs => andB (symOK xs j 0) (symOK xs j 1)

@[expose] noncomputable def relRepF (j q h : ℕ) : ℕ :=
  nthN dRelRep (Nat.add (Nat.add (Nat.mul 4 j) (Nat.mul 2 q)) h)

@[expose] noncomputable def quadX (j q t : ℕ) : ℕ :=
  xC j (Nat.div (relRepF j q (Nat.div t 2)) 3) (Nat.mod (relRepF j q (Nat.div t 2)) 3) (Nat.mod t 2)

@[expose] noncomputable def rootW (r : ℕ) : List (ℕ × Bool) := nthWd (splitW dRelR) r

@[expose] noncomputable def relEx (r : ℕ) : ℕ := nthN dRelE r

@[expose] noncomputable def relOKM (Y : List ℕ) : Bool :=
  allN 20 fun r => Nat.beq (powM (wordC (nthN Y) (nthN Y) (rootW r)) (relEx r)) idM

@[noinline, expose] noncomputable def chkRelM (j q : ℕ) : Bool := buildL 4 (quadX j q) relOKM

@[expose] noncomputable def inX (j q : ℕ) : ℕ :=
  xC j (Nat.div q 2) (rowAt j 0 (Nat.div q 2)) (Nat.mod q 2)

@[expose] noncomputable def inProg (j : ℕ) : List (List (ℕ × Bool)) := splitW (selJ j dInP0 dInP1)

@[expose] noncomputable def inTg (j i : ℕ) : ℕ := nthN (selJ j dInT0 dInT1) i

@[noinline, expose] noncomputable def chkInM (j : ℕ) : Bool :=
  buildL 4 (inX j) fun xs => runK (inProg j) xs xs fun F _ =>
    allN 4 fun i => Nat.beq (nthN F (inTg j i)) (inX j (4 + i))

@[expose] noncomputable def topBL (j : ℕ) : ℕ := nthN dTopB (Nat.mul 2 j)

@[expose] noncomputable def topBM (j : ℕ) : ℕ := nthN dTopB (Nat.add (Nat.mul 2 j) 1)

@[expose] noncomputable def topX (j q : ℕ) : ℕ :=
  ifN (Nat.blt 3 q) (xC j (topBL j) (topBM j) (Nat.sub q 4)) (inX j q)

@[expose] noncomputable def topProg (j : ℕ) : List (List (ℕ × Bool)) := splitW (selJ j dTopP0 dTopP1)

@[expose] noncomputable def topTg (j i : ℕ) : ℕ := nthN (selJ j dTopT0 dTopT1) i

@[noinline, expose] noncomputable def chkTopM (j : ℕ) : Bool :=
  buildL 6 (topX j) fun xs => runK (topProg j) xs xs fun F _ =>
    allN 8 fun i => Nat.beq (nthN F (topTg j i)) (rM i)

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.L3Seven
