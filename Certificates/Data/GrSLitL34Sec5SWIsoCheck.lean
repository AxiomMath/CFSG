module

public import Certificates.Data.GrSLitL34FactsRealBCheck

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts.Real.WIso

open CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.ComponentClassification.GrSLit.L34Facts

@[expose] def kIdx (i j : ZMod 4) : ℕ := 4 * i.val + j.val

@[expose] def inKB (kb : List Bool) (i j : ZMod 4) : Bool := kb.getD (kIdx i j) false

@[expose] def eqKB (kb : List Bool) (x y : MElt) : Bool :=
  x.1 == y.1 && inKB kb (x.2.1 - y.2.1) (x.2.2 - y.2.2)

@[expose] def kbOfMask (m : ℕ) : List Bool := (List.range 16).map m.testBit

@[expose] def kbMasks : List ℕ :=
  [1, 5, 257, 1025, 15, 1285, 2565, 4369, 33825, 16705, 9345, 3855, 21845, 42405, 65535]

@[expose] def kbList : List (List Bool) := kbMasks.map kbOfMask

@[expose] def z4 : List (ZMod 4) := [0, 1, 2, 3]

@[expose] def isSubKB (kb : List Bool) : Bool :=
  kb.length == 16 && inKB kb 0 0 &&
    z4.all fun a => z4.all fun b => z4.all fun c => z4.all fun d =>
      !(inKB kb a b && inKB kb c d) || inKB kb (a + c) (b + d)

@[expose] def allBool : ℕ → List (List Bool)
  | 0 => [[]]
  | n + 1 => (allBool n).flatMap fun l => [false :: l, true :: l]

@[noinline, expose] def kClassOK : Bool :=
  (allBool 16).all fun kb => !isSubKB kb || kbList.contains kb

@[expose] def kbZero (kb : List Bool) : Bool := kb == kbOfMask 1

@[expose] def kbFull (kb : List Bool) : Bool := kb == kbOfMask 65535

@[expose] def kbCyc (kb : List Bool) : Bool :=
  z4.any fun g₁ => z4.any fun g₂ => z4.all fun i => z4.all fun j =>
    z4.any fun m => inKB kb (i - m * g₁) (j - m * g₂)

@[expose] def liftsKB (kb : List Bool) (i : ℕ) : Bool :=
  z4.all fun a => z4.all fun b => !inKB kb a b ||
    inKB kb (a * ((alphaEntry i 64).2.1 : ZMod 4) + b * ((alphaEntry i 65).2.1 : ZMod 4))
      (a * ((alphaEntry i 64).2.2.1 : ZMod 4) + b * ((alphaEntry i 65).2.2.1 : ZMod 4))

@[expose] def yTab (t i : ℕ) : Tab := comp 42 (wordTab (tg t)) (repTab i)

@[expose] def outerInvs : List (ℕ × ℕ) :=
  (List.range 36).flatMap fun i => if repInS.contains i then [] else
    ((List.range 64).filter fun t => comp 42 (yTab t i) (yTab t i) == idTab 42).map fun t => (t, i)

@[expose] def esS : Enum := enumBFS 42 gensS 20160

@[expose] def idxS : Std.HashMap Tab ℕ := indexOf esS.tabs

@[expose] def inSB (x : Tab) : Bool := found idxS esS.tabs x

@[expose] def pairOK (p p' : ℕ × ℕ) : Bool :=
  comp 42 (yTab p.1 p.2) (yTab p'.1 p'.2) == comp 42 (yTab p'.1 p'.2) (yTab p.1 p.2) &&
    !inSB (comp 42 (yTab p.1 p.2) (yTab p'.1 p'.2))

@[expose] def rhoTab (lab : ℕ) : Tab := if lab = 0 then r₂T else if lab = 1 then r₃T else r₄T

@[expose] def conjOK (t i lab t' j : ℕ) : Bool :=
  (invTab 42 (yTab t' j)).size == 42 && comp 42 (invTab 42 (yTab t' j)) (yTab t' j) == idTab 42 &&
    comp 42 (comp 42 (yTab t' j) (yTab t i)) (invTab 42 (yTab t' j)) == rhoTab lab

@[expose] def outerTypes : List ((ℕ × ℕ) × ℕ × ℕ × ℕ) := [
    ((0, 1), 0, 0, 0), ((1, 1), 0, 2, 0), ((4, 1), 0, 8, 0), ((5, 1), 0, 10, 0),
    ((16, 1), 0, 20, 0), ((28, 1), 0, 21, 0), ((49, 1), 0, 22, 0), ((61, 1), 0, 23, 0),
    ((0, 2), 1, 0, 0), ((4, 2), 1, 17, 0), ((8, 2), 1, 23, 0), ((12, 2), 1, 26, 0),
    ((17, 2), 1, 16, 0), ((23, 2), 1, 20, 0), ((26, 2), 1, 24, 0), ((29, 2), 1, 1, 0),
    ((34, 2), 1, 19, 0), ((39, 2), 1, 18, 0), ((43, 2), 1, 25, 0), ((46, 2), 1, 2, 0),
    ((49, 2), 1, 27, 0), ((54, 2), 1, 21, 0), ((59, 2), 1, 3, 0), ((61, 2), 1, 22, 0),
    ((0, 3), 2, 0, 0), ((4, 3), 2, 8, 0), ((17, 3), 2, 9, 0), ((22, 3), 2, 10, 0),
    ((27, 3), 2, 11, 0), ((29, 3), 2, 1, 0), ((42, 3), 2, 2, 0), ((55, 3), 2, 3, 0),
    ((0, 6), 0, 0, 4), ((2, 6), 0, 2, 4), ((4, 6), 0, 8, 4), ((6, 6), 0, 10, 4),
    ((20, 6), 0, 20, 4), ((38, 6), 0, 23, 4), ((40, 6), 0, 21, 4), ((58, 6), 0, 22, 4),
    ((0, 7), 1, 0, 4), ((4, 7), 1, 17, 4), ((8, 7), 1, 23, 4), ((12, 7), 1, 26, 4),
    ((19, 7), 1, 24, 4), ((22, 7), 1, 16, 4), ((25, 7), 1, 20, 4), ((31, 7), 1, 21, 4),
    ((33, 7), 1, 3, 4), ((38, 7), 1, 22, 4), ((42, 7), 1, 1, 4), ((45, 7), 1, 18, 4),
    ((51, 7), 1, 19, 4), ((53, 7), 1, 25, 4), ((58, 7), 1, 27, 4), ((63, 7), 1, 2, 4),
    ((0, 8), 0, 0, 5), ((3, 8), 0, 2, 5), ((4, 8), 0, 8, 5), ((7, 8), 0, 10, 5),
    ((24, 8), 0, 20, 5), ((35, 8), 0, 22, 5), ((47, 8), 0, 23, 5), ((52, 8), 0, 21, 5),
    ((0, 9), 1, 0, 5), ((4, 9), 1, 17, 5), ((8, 9), 1, 23, 5), ((12, 9), 1, 26, 5),
    ((18, 9), 1, 20, 5), ((21, 9), 1, 24, 5), ((27, 9), 1, 16, 5), ((30, 9), 1, 25, 5),
    ((35, 9), 1, 27, 5), ((37, 9), 1, 2, 5), ((41, 9), 1, 21, 5), ((47, 9), 1, 22, 5),
    ((50, 9), 1, 3, 5), ((55, 9), 1, 1, 5), ((57, 9), 1, 19, 5), ((62, 9), 1, 18, 5),
    ((0, 15), 0, 0, 12), ((3, 15), 0, 2, 12), ((12, 15), 0, 8, 12), ((15, 15), 0, 10, 12),
    ((16, 15), 0, 20, 12), ((31, 15), 0, 22, 12), ((51, 15), 0, 23, 12), ((60, 15), 0, 21, 12),
    ((0, 17), 0, 0, 14), ((1, 17), 0, 2, 14), ((12, 17), 0, 8, 14), ((13, 17), 0, 10, 14),
    ((20, 17), 0, 20, 14), ((36, 17), 0, 21, 14), ((41, 17), 0, 22, 14), ((57, 17), 0, 23, 14),
    ((0, 20), 0, 0, 13), ((1, 20), 0, 2, 13), ((8, 20), 0, 8, 13), ((9, 20), 0, 10, 13),
    ((24, 20), 0, 20, 13), ((32, 20), 0, 21, 13), ((45, 20), 0, 22, 13), ((53, 20), 0, 23, 13),
    ((0, 22), 0, 0, 15), ((2, 22), 0, 2, 15), ((8, 22), 0, 8, 15), ((10, 22), 0, 10, 15),
    ((16, 22), 0, 20, 15), ((30, 22), 0, 22, 15), ((48, 22), 0, 21, 15), ((62, 22), 0, 23, 15),
    ((0, 26), 0, 8, 24), ((2, 26), 0, 21, 24), ((12, 26), 0, 0, 24), ((14, 26), 0, 20, 24),
    ((24, 26), 0, 10, 24), ((34, 26), 0, 23, 24), ((44, 26), 0, 2, 24), ((54, 26), 0, 22, 24),
    ((0, 29), 2, 0, 13), ((8, 29), 2, 8, 13), ((18, 29), 2, 10, 13), ((23, 29), 2, 11, 13),
    ((25, 29), 2, 9, 13), ((33, 29), 2, 1, 13), ((50, 29), 2, 2, 13), ((59, 29), 2, 3, 13),
    ((0, 32), 0, 0, 26), ((3, 32), 0, 2, 26), ((8, 32), 0, 8, 26), ((11, 32), 0, 10, 26),
    ((20, 32), 0, 20, 26), ((39, 32), 0, 23, 26), ((43, 32), 0, 22, 26), ((56, 32), 0, 21, 26),
    ((0, 35), 2, 0, 12), ((12, 35), 2, 8, 12), ((19, 35), 2, 9, 12), ((21, 35), 2, 10, 12),
    ((26, 35), 2, 11, 12), ((37, 35), 2, 2, 12), ((46, 35), 2, 3, 12), ((63, 35), 2, 1, 12)]

@[expose] def typeOf (t i : ℕ) : ℕ := ((outerTypes.find? fun e => e.1 == (t, i)).map (·.2.1)).getD 3

@[noinline, expose] def typesOK : Bool :=
  outerTypes.map (·.1) == outerInvs &&
    outerTypes.all fun e => decide (e.2.1 < 3) && decide (e.2.2.2 < 36) &&
      conjOK e.1.1 e.1.2 e.2.1 e.2.2.1 e.2.2.2

@[noinline, expose] def typePairOK : Bool :=
  outerTypes.all fun e => outerTypes.all fun e' => !pairOK e.1 e'.1 || e.2.1 != e'.2.1

@[expose] def isInvKB (kb : List Bool) (x : MElt) : Bool :=
  eqKB kb (mulM x x) oneM && !eqKB kb x oneM

@[expose] def fixKB (kb : List Bool) (t i : ℕ) (x : MElt) : Bool := eqKB kb (betaYM t i x) x

@[expose] def dedupKB (kb : List Bool) (L : List MElt) : List MElt :=
  L.foldl (fun acc x => if acc.any (eqKB kb x) then acc else acc ++ [x]) []

@[expose] def fixInvs (kb : List Bool) (t i : ℕ) : List MElt :=
  allM.filter fun x => fixKB kb t i x && isInvKB kb x

@[noinline, expose] def d1K (kb : List Bool) : Bool :=
  outerInvs.all fun p => !liftsKB kb p.2 ||
    let F := fixInvs kb p.1 p.2
    outerInvs.all fun p' => !liftsKB kb p'.2 || !pairOK p p' ||
      2 ≤ (dedupKB kb (F.filter fun x => fixKB kb p'.1 p'.2 x)).length

@[expose] def kVals (t i : ℕ) : List ℕ :=
  (List.range 64).filter fun k =>
    k == 0 || ((mulM (k, 0, 0) (k, 0, 0)).1 == 0 && (betaYM t i (k, 0, 0)).1 == k)

@[expose] def expType (kb : List Bool) : ℕ := if kbZero kb then 0 else 2

@[expose] def dCase (kb : List Bool) (t i k : ℕ) (F : List MElt) : Bool :=
  let I := F.filter fun x => eqKB kb (mulM x (k, 0, 0)) (mulM (k, 0, 0) x)
  (I.any fun x => x.1 != 0 && x.1 != k) || 4 ≤ (dedupKB kb I).length ||
    (k != 0 && typeOf t i == expType kb && (kbZero kb || kbCyc kb) &&
      (kbFull kb || 3 ≤ (dedupKB kb I).length))

@[noinline, expose] def dK (kb : List Bool) : Bool :=
  outerInvs.all fun p => !liftsKB kb p.2 ||
    let F := fixInvs kb p.1 p.2
    (kVals p.1 p.2).all fun k => dCase kb p.1 p.2 k F

end CFSG.ComponentClassification.GrSLit.L34Facts.Real.WIso
