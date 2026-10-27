
module

public import CFSG.Sporadic.Schreier.TitsAbelCheckInputs
public import CFSG.Quasithin.Recognition.CertTwoF4CheckInputs

public section

namespace Certificates.TitsAschbacherParrott

open CFSG.Sporadic.Schreier.Tits CFSG.Monster.B.Co2.Native CFSG.Quasithin

@[expose] def prodArr (A : Array (Array ℕ)) (l : List ℕ) : Array ℕ :=
  l.foldr (fun i a => compA 1755 A[i]! a) (idA 1755)

@[expose] def eltArr (A : Array (Array ℕ)) (w : List ℕ) (o : Bool) : Array ℕ :=
  compA 1755 (prodArr A w) (if o then titsPiArr else idA 1755)

@[expose] def powA (a : Array ℕ) (k : ℕ) : Array ℕ :=
  (List.replicate k a).foldr (compA 1755) (idA 1755)

@[expose] def commEqA (x y r : Array ℕ) : Bool :=
  eqA 1755 (compA 1755 x y) (compA 1755 (compA 1755 y x) r)

@[expose] def conjEqA (w a b : Array ℕ) : Bool :=
  eqA 1755 (compA 1755 a w) (compA 1755 w b)

@[expose] def lettersIn (lo hi : ℕ) (w : List ℕ) : Bool := w.all fun l => lo ≤ l && l ≤ hi

@[expose] def parrottWords : List (List ℕ × Bool) :=
  [([], false), ([1, 2, 0, 2, 0, 0], true), ([2, 2, 0, 1, 1, 0, 1, 1], false),
   ([0, 1, 2, 0, 0, 0], false), ([1, 0, 1, 1, 0, 1, 1, 0, 0], true), ([2, 2, 1, 1], true),
   ([0, 0, 0, 2, 0, 1, 2], true), ([1, 0, 0, 2, 1, 2, 0, 0], false),
   ([0, 0, 0, 1, 1, 0], false), ([1, 2, 0, 2, 0, 0, 0], false),
   ([2, 1, 0, 2, 1, 1, 0, 0, 0], false), ([0, 0, 0, 0], false), ([2, 2], false)]

@[expose] def vArrs : Array (Array ℕ) := Array.ofFn (n := 13) fun i =>
  eltArr titsSArrs (parrottWords.getD i.val ([], false)).1 (parrottWords.getD i.val ([], false)).2

@[expose] def vA (i : ℕ) : Array ℕ := vArrs[i]!

@[expose] def vProd (l : List ℕ) : Array ℕ := prodArr vArrs l

@[expose] def parrottSq (i : ℕ) : List ℕ :=
  if i = 1 then [2] else if i = 4 then [8] else if i = 5 then [12] else if i = 6 then [11] else []

@[expose] def parrottComm : List (ℕ × ℕ × List ℕ) :=
  [(11, 3, [12]), (10, 4, [12]), (9, 6, [12]), (8, 7, [12]),
   (10, 1, [11]), (9, 2, [11]),
   (9, 1, [10, 11, 12]), (8, 2, [10, 11, 12]),
   (8, 1, [9, 11, 12]),
   (5, 7, [11]), (5, 6, [10]),
   (5, 4, [9]), (5, 3, [8]),
   (7, 4, [10, 11, 12]), (7, 3, [9, 10]),
   (6, 3, [8, 9, 12]), (6, 1, [7]),
   (4, 2, [7, 11, 12]), (4, 1, [5, 6, 7, 9, 11, 12]),
   (3, 2, [5, 6, 7, 8, 9, 10, 12]),
   (3, 1, [4, 5, 7, 8, 9, 10, 11, 12])]

@[expose] def parrottPairs : List (ℕ × ℕ) := parrottComm.map fun r => (r.1, r.2.1)

@[expose] def listed (i j : ℕ) : Bool := parrottComm.any fun r => r.1 == i && r.2.1 == j

@[expose] def sqOK : Bool :=
  (List.range' 1 12).all fun i => eqA 1755 (compA 1755 (vA i) (vA i)) (vProd (parrottSq i))

@[expose] def neOneOK : Bool := (List.range' 1 12).all fun i => !eqA 1755 (vA i) (idA 1755)

@[expose] def commOK : Bool := parrottComm.all fun r => commEqA (vA r.1) (vA r.2.1) (vProd r.2.2)

@[expose] def commuteOK : Bool :=
  (List.range' 1 12).all fun i => (List.range' 1 12).all fun j =>
    listed i j || listed j i || commEqA (vA i) (vA j) (idA 1755)

@[expose] def relCheck : Bool :=
  sqOK && neOneOK && commOK && commuteOK && eqA 1755 (vA 12) titsZArr

@[expose] def sInV : List (List ℕ) := [[2, 8, 5, 1], [11, 8, 4, 5], [5, 3, 7, 6]]

@[expose] def piInV : List ℕ := [4, 5, 4]

@[expose] def sInW : List (List (List ℕ)) :=
  [[[2], [8], [1, 5]], [[4, 5], [11], [8]], [[6, 5], [7], [8], [3]]]

@[expose] def jInU : List (List ℕ) := [[11, 8, 4, 5], [5, 3, 7, 6], [10, 8, 7], [3, 5, 7, 4]]

@[expose] def piInU : List ℕ := [4, 5, 4]

@[expose] def inDelta (i : ℕ) : Bool := i == 1 || i == 4 || i == 5 || i == 6

@[expose] def blockOK : List ℕ → Bool
  | [k] => 1 ≤ k && k ≤ 12 && !inDelta k
  | [i, j] => inDelta i && inDelta j
  | _ => false

@[expose] def inJ (a : Array ℕ) : Bool := siftA 1755 titsJLevels (baseArr 1755 titsJBase) 0 a

@[expose] def u8Bits (a : ℕ) : List ℕ :=
  (List.range 5).filterMap fun k => if a.testBit k then some (8 + k) else none

@[expose] def genCheck : Bool :=
  (List.range 3).all (fun j => eqA 1755 titsSArrs[j]! (vProd (sInV.getD j []))) &&
    eqA 1755 titsPiArr (vProd piInV) && sInV.all (lettersIn 1 12) && lettersIn 1 12 piInV &&
    (List.range 3).all (fun j => eqA 1755 titsSArrs[j]! (vProd (sInW.getD j []).flatten)) &&
    sInW.all (fun bs => bs.all blockOK) &&
    (List.range' 3 10).all (fun i =>
      inJ (compA 1755 (vA i) (if (parrottWords.getD i ([], false)).2 then piInv else idA 1755))) &&
    (List.range 4).all (fun k => eqA 1755 titsJArrs[k]! (vProd (jInU.getD k []))) &&
    eqA 1755 titsPiArr (vProd piInU) && jInU.all (lettersIn 3 12) && lettersIn 3 12 piInU &&
    (List.range 32).all fun a => (List.range 32).all fun b =>
      a == b || !eqA 1755 (vProd (u8Bits a)) (vProd (u8Bits b))

@[expose] def reeWord₁ : List ℕ := [0, 0, 2, 2, 0, 0, 1, 0, 2]

@[expose] def reeWord₂ : List ℕ := [3, 2, 2, 0]

@[expose] def w1Arr : Array ℕ := prodArr titsHArrs reeWord₁

@[expose] def w2Arr : Array ℕ := prodArr titsNArrs reeWord₂

@[expose] def reeConj₁ : List (ℕ × ℕ) := [(11, 8), (10, 9), (7, 3), (6, 4)]

@[expose] def reeConj₂ : List (ℕ × ℕ) := [(12, 11), (2, 8), (7, 9), (1, 4), (5, 6)]

@[expose] def hInTW : List (List ℕ) :=
  [[13, 2, 9, 1, 13, 6], [5, 3, 2, 1, 13, 4, 1], [2, 8, 5, 1]]

@[expose] def nInTW : List (List ℕ) :=
  [[2, 8, 5, 1], [11, 8, 4, 5], [5, 3, 7, 6], [13, 2, 1, 8, 5, 2]]

@[expose] def notInT (a : Array ℕ) : Bool := !inS a && !inS (compA 1755 a piInv)

@[expose] def reeCheck : Bool :=
  reeConj₁.all (fun p => conjEqA w1Arr (vA p.1) (vA p.2)) &&
    reeConj₂.all (fun p => conjEqA w2Arr (vA p.1) (vA p.2)) &&
    eqA 1755 (compA 1755 w1Arr w1Arr) (idA 1755) && !eqA 1755 w1Arr (idA 1755) &&
    eqA 1755 (compA 1755 w2Arr w2Arr) (idA 1755) && !eqA 1755 w2Arr (idA 1755) &&
    !eqA 1755 (powA (compA 1755 w1Arr w2Arr) 4) (idA 1755) &&
    eqA 1755 (powA (compA 1755 w1Arr w2Arr) 8) (idA 1755) &&
    (List.range 8).all (fun k => (k == 0 || notInT (powA (compA 1755 w1Arr w2Arr) k)) &&
      notInT (compA 1755 (powA (compA 1755 w1Arr w2Arr) k) w1Arr)) &&
    (List.range 3).all (fun k =>
      eqA 1755 titsHArrs[k]! (prodArr (vArrs.push w1Arr) (hInTW.getD k []))) &&
    (List.range 4).all (fun k =>
      eqA 1755 titsNArrs[k]! (prodArr (vArrs.push w2Arr) (nInTW.getD k []))) &&
    hInTW.all (lettersIn 1 13) && nInTW.all (lettersIn 1 13)

@[expose] def hatXWord : List ℕ := [0, 0, 1, 2, 1, 0]

@[expose] def xArr : Array ℕ := prodArr titsHArrs hatXWord

@[expose] def xCheck : Bool :=
  eqA 1755 (powA xArr 5) (idA 1755) && !eqA 1755 xArr (idA 1755) &&
    eqA 1755 (compA 1755 (vA 1) xArr) (compA 1755 (powA xArr 3) (vA 1)) &&
    commEqA (vA 5) xArr (idA 1755) &&
    allLt 1024 fun i => !commEqA pPel[i]! xArr (idA 1755) ||
      [idA 1755, vA 5, vA 12, compA 1755 (vA 5) (vA 12)].any (eqA 1755 pPel[i]!)

end Certificates.TitsAschbacherParrott
