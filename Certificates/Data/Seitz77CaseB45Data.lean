module

public import Certificates.Data.CFSGNative.PSL3Four.Basic

public section

namespace Certificates.Seitz77CaseB45

open CFSG.PSL3Four.Native

@[expose] def uGens : Array Tab :=
  #[
    #[20, 12, 16, 1, 8, 15, 5, 2, 10, 3, 14, 7, 9, 6, 4, 13, 11, 17, 19, 18, 0, 35, 23, 38, 32,
     29, 28, 24, 30, 41, 33, 25, 40, 26, 34, 21, 37, 36, 39, 22, 27, 31],
    #[20, 9, 14, 3, 7, 13, 6, 4, 11, 1, 16, 8, 12, 5, 2, 15, 10, 17, 19, 18, 0, 21, 39, 38, 41,
     40, 33, 31, 30, 32, 28, 27, 29, 26, 34, 35, 36, 37, 23, 22, 25, 24],
    #[18, 4, 15, 8, 9, 7, 2, 13, 12, 10, 1, 6, 14, 16, 3, 11, 5, 17, 0, 20, 19, 37, 41, 29, 33,
     22, 32, 26, 24, 39, 27, 23, 30, 40, 34, 36, 35, 21, 25, 31, 28, 38],
    #[20, 10, 15, 2, 5, 16, 8, 1, 12, 4, 13, 6, 11, 7, 3, 14, 9, 17, 19, 18, 0, 37, 28, 38, 25,
     31, 23, 40, 30, 27, 39, 32, 24, 26, 34, 36, 35, 21, 33, 22, 41, 29]
  ]

@[expose] def tlGens : Array Tab :=
  #[
    #[18, 4, 15, 8, 9, 7, 2, 13, 12, 10, 1, 6, 14, 16, 3, 11, 5, 17, 0, 20, 19, 37, 41, 29, 33,
     22, 32, 26, 24, 39, 27, 23, 30, 40, 34, 36, 35, 21, 25, 31, 28, 38],
    #[37, 39, 32, 24, 26, 33, 29, 22, 41, 23, 30, 27, 40, 28, 25, 31, 38, 34, 36, 35, 21, 20,
     7, 9, 3, 14, 4, 11, 13, 6, 10, 15, 2, 5, 17, 19, 18, 0, 16, 1, 12, 8],
    #[21, 25, 22, 23, 24, 41, 39, 40, 38, 27, 29, 26, 28, 32, 30, 33, 31, 34, 36, 35, 37, 18,
     13, 7, 12, 2, 5, 11, 16, 3, 1, 6, 14, 10, 17, 20, 0, 19, 9, 4, 15, 8]
  ]

@[expose] def etl : Enum := enumBFS 42 tlGens 256

@[expose] def eu : Enum := enumBFS 42 uGens 64

@[expose] def idxTL : Std.HashMap Tab Nat := indexOf etl.tabs

@[expose] def mtArr : Array Nat := Id.run do
  let mut r : Array Nat := Array.mkEmpty 65536
  for i in [0:256] do
    for j in [0:256] do
      r := r.push (posOf idxTL etl.tabs (comp 42 etl.tabs[i]! etl.tabs[j]!))
  return r

@[expose] def mtF (i j : Nat) : Nat := mtArr[256 * i + j]!

@[expose] def isUArr : Array Bool :=
  etl.tabs.map fun t => eu.tabs.contains t

@[expose] def invArr : Array Nat :=
  (Array.range 256).map fun i => ((List.range 256).find? fun j => mtF i j == 0).getD 0

@[expose] def repArr : Array Nat :=
  (Array.range 256).map fun i =>
    ((List.range 256).find? fun j => isUArr[mtF invArr[j]! i]!).getD i

@[expose] def repsArr : Array Nat :=
  ((List.range 256).filter fun i => repArr[i]! == i).toArray

@[expose] def labArr : Array Nat :=
  repArr.map fun r => (repsArr.findIdx? (· == r)).getD 0

@[expose] def labF (i : Nat) : Nat := labArr[i]!

@[expose] def isUF (i : Nat) : Bool := isUArr[i]!

@[expose] def laddF (p q : Nat) : Nat := labF (mtF repsArr[p]! repsArr[q]!)

@[expose] def tablesOK : Bool :=
  enumOK 42 tlGens etl && etl.tabs.size == 256 && enumOK 42 uGens eu && eu.tabs.size == 64 &&
  (allBelow 64 fun k => etl.tabs.contains eu.tabs[k]!) &&
  mtArr.size == 65536 &&
  (allBelow 256 fun i => allBelow 256 fun j =>
    mtF i j < 256 && etl.tabs[mtF i j]! == comp 42 etl.tabs[i]! etl.tabs[j]!) &&
  (allBelow 256 fun i => invArr[i]! < 256 && mtF i invArr[i]! == 0) &&
  repsArr.size == 4 && labArr.size == 256 &&
  (allBelow 256 fun i => labF i < 4) &&
  (allBelow 4 fun p => repsArr[p]! < 256 && labF repsArr[p]! == p) &&
  labF 0 == 0 &&
  (allBelow 256 fun i => allBelow 256 fun j =>
    (labF i == labF j) == isUF (mtF invArr[i]! j)) &&
  (allBelow 256 fun i => allBelow 256 fun j =>
    labF (mtF i j) == laddF (labF i) (labF j))

@[expose] def extE (mt : Nat → Nat → Nat) (E : List Nat) (y : Nat) : List Nat :=
  E ++ E.map (mt y)

@[expose] def maxE (E : List Nat) : Nat := E.foldl max 0

@[expose] def invsOf (mt : Nat → Nat → Nat) : List Nat :=
  (List.range 256).filter fun i => i != 0 && mt i i == 0

@[expose] def nextLevel (mt : Nat → Nat → Nat) (invs : List Nat) (L : List (List Nat)) :
    List (List Nat) :=
  L.flatMap fun E =>
    (invs.filter fun y => maxE E < y && E.all fun e => mt y e == mt e y).map (extE mt E)

@[expose] def levelE (mt : Nat → Nat → Nat) (invs : List Nat) : Nat → List (List Nat)
  | 0 => [[0]]
  | k + 1 => nextLevel mt invs (levelE mt invs k)

@[expose] def fb7Aux (mt : Nat → Nat → Nat) (isU : Nat → Bool) (invs : List Nat)
    (L4 : List (List Nat)) : Bool :=
  (nextLevel mt invs L4).isEmpty && L4.all fun E => E.all isU

@[expose] def fb7Check (mt : Nat → Nat → Nat) (isU : Nat → Bool) : Bool :=
  fb7Aux mt isU (invsOf mt) (levelE mt (invsOf mt) 4)

abbrev WEl : Type := Nat × Nat × Bool

@[expose] def wmul (mt : Nat → Nat → Nat) (x y : WEl) : WEl :=
  if x.2.2 then (mt x.1 y.2.1, mt x.2.1 y.1, !y.2.2) else (mt x.1 y.1, mt x.2.1 y.2.1, y.2.2)

@[expose] def wone : WEl := (0, 0, false)

@[expose] def wOrd (mt : Nat → Nat → Nat) (w : WEl) : Nat :=
  if w == wone then 1 else
  let w2 := wmul mt w w
  if w2 == wone then 2 else
  let w4 := wmul mt w2 w2
  if w4 == wone then 4 else
  let w8 := wmul mt w4 w4
  if w8 == wone then 8 else
  if wmul mt w8 w8 == wone then 16 else 0

@[expose] def ordStats (mt : Nat → Nat → Nat) (L : List WEl) : List Nat :=
  let ords := L.map (wOrd mt)
  [2, 4, 8, 16].map fun k => (ords.filter fun o => o == k).length

@[expose] def zOf (mt : Nat → Nat → Nat) (L : List WEl) : Nat :=
  (L.filter fun w => L.all fun v => wmul mt w v == wmul mt v w).length

@[expose] def differs (mt : Nat → Nat → Nat) (L : List WEl) (len : Nat) (os : List Nat)
    (zt : Nat) : Bool :=
  L.length != len || ordStats mt L != os || zOf mt L != zt

@[expose] def inM (m p q : Nat) : Bool := m.testBit (4 * p + q)

@[expose] def admM (ladd : Nat → Nat → Nat) (m : Nat) : Bool :=
  inM m 0 0 &&
  (allBelow 4 fun p => allBelow 4 fun q => !(inM m p q) || (inM m q p &&
    (allBelow 4 fun p' => allBelow 4 fun q' =>
      !(inM m p' q') || inM m (ladd p p') (ladd q q'))))

@[expose] def tauList (lab : Nat → Nat) (m : Nat) : List WEl :=
  let F := (List.range 256).filter fun c => inM m (lab c) (lab c)
  (F.map fun c => (c, c, false)) ++ (F.map fun c => (c, c, true))

@[expose] def byLabel (lab : Nat → Nat) (m p : Nat) (L : List Nat) : List Nat :=
  L.filter fun d => inM m p (lab d)

@[expose] def cenBase (mt : Nat → Nat → Nat) (lab : Nat → Nat) (m a b : Nat) : List WEl :=
  let cenB := (List.range 256).filter fun d => mt b d == mt d b
  let cenBp := (List.range 4).map fun p => byLabel lab m p cenB
  ((List.range 256).filter fun c => mt a c == mt c a).flatMap fun c =>
    (cenBp.getD (lab c) []).map fun d => (c, d, false)

@[expose] def cenSwap (mt : Nat → Nat → Nat) (lab : Nat → Nat) (m a b : Nat) : List WEl :=
  let swB := (List.range 256).filter fun d => mt b d == mt d a
  let swBp := (List.range 4).map fun p => byLabel lab m p swB
  ((List.range 256).filter fun c => mt a c == mt c b).flatMap fun c =>
    (swBp.getD (lab c) []).map fun d => (c, d, true)

@[expose] def cenList (mt : Nat → Nat → Nat) (lab : Nat → Nat) (m a b : Nat) : List WEl :=
  cenBase mt lab m a b ++ cenSwap mt lab m a b

@[expose] def mainAux (mt : Nat → Nat → Nat) (lab : Nat → Nat) (m : Nat) (invs : List Nat)
    (len : Nat) (os : List Nat) (zt : Nat) : Bool :=
  invs.all fun a => invs.all fun b =>
    (a == 0 && b == 0) || !(inM m (lab a) (lab b)) ||
      differs mt (cenList mt lab m a b) len os zt

@[expose] def mainOK (mt : Nat → Nat → Nat) (lab : Nat → Nat) (m : Nat) : Bool :=
  mainAux mt lab m ((List.range 256).filter fun i => mt i i == 0)
    (tauList lab m).length (ordStats mt (tauList lab m)) (zOf mt (tauList lab m))

@[expose] def fb6Check (mt : Nat → Nat → Nat) (lab : Nat → Nat) (ladd : Nat → Nat → Nat) : Bool :=
  (List.range 65536).all fun m => !(admM ladd m) || mainOK mt lab m

@[expose] def fbSixCheck : Bool :=
  tablesOK && fb7Check mtF isUF && fb6Check mtF labF laddF

end Certificates.Seitz77CaseB45
