module

public import Certificates.Data.Holder1711.Om1Data
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.WeylTData
public import CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977Commuting
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.WeylData
public import CFSG.RankThree.Native.PermEnumeration

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om1Check

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native
open CFSG.EvenSmallLie.OmegaEight CFSG.EvenSmallLie.OmegaEight.Weyl
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om1Data

@[expose] def reflTab (_ : Unit := ()) : Array (Array ℕ) := (Array.range 240).map reflArr

@[expose] def wA (RT : Array (Array ℕ)) : List ℕ → Array ℕ
  | [] => idA 240
  | r :: l => compA 240 RT[r]! (wA RT l)

@[expose] def wordOK (w : List ℕ) : Bool := w.all (· < 240) && w.length % 2 == 0

@[expose] def wsA (RT : Array (Array ℕ)) (ws : List (List ℕ)) : Array (Array ℕ) :=
  (ws.map (wA RT)).toArray

@[expose] def repMasks : List ℕ := [15, 3, 252, 23]

@[expose] def eA (m : ℕ) : Array ℕ := frameArr (frameDecode m)

@[expose] def zA : Array ℕ := negArr

@[expose] def wT : List (List ℕ) := wS0 ++ wP3

@[expose] def wCa : List (List ℕ) := wSa ++ wPa3 ++ wPa5

@[expose] def wCc : List (List ℕ) := wSc ++ wPc

@[expose] def withPairs (ws : List (List ℕ)) : List (List ℕ) :=
  [] :: (ws ++ ws.flatMap fun a => ws.map fun b => a ++ b)

@[expose] def commOK (x y : Array ℕ) : Bool := eqA 240 (compA 240 x y) (compA 240 y x)

@[expose] def allWords : List (List ℕ) :=
  [wT0, wI0, wJ0, wS1, wG1] ++ wS0 ++ wP3 ++ wSa ++ wPa3 ++ wPa5 ++ wSc ++ wPc ++ wX ++
    wSub ++ wDT ++ maskData.map (·.2.2)

@[expose] def wordsCheck (RT : Array (Array ℕ)) : Bool :=
  allWords.all fun w => wordOK w && validA 240 (wA RT w)

@[expose] def relCheck (RT : Array (Array ℕ)) : Bool :=
  let t0 := eA 15
  let i0 := wA RT wI0
  let j0 := wA RT wJ0
  eqA 240 (wA RT wT0) t0 &&
  eqA 240 (compA 240 i0 i0) t0 && eqA 240 (compA 240 j0 j0) t0 &&
  eqA 240 (conjA 240 j0 i0) (invCand 240 i0) &&
  validA 240 i0 && validA 240 j0 &&
  eqA 240 (conjA 240 (wA RT wG1) t0) (compA 240 t0 zA) &&
  validA 240 (wA RT wG1) && validA 240 (wA RT wS1) &&
  (wT ++ [wS1]).all (fun w => commOK (wA RT w) t0) &&
  wCa.all (fun w => commOK (wA RT w) (eA 3)) &&
  wCc.all (fun w => commOK (wA RT w) (eA 23)) &&
  eqA 240 (eA 252) (compA 240 zA (eA 3))

@[expose] def enumOf (RT : Array (Array ℕ)) (ws : List (List ℕ)) (fuel : ℕ) : ArrCert :=
  enumBfs 240 (wsA RT ws) keyPts fuel

@[expose] def enumSize (RT : Array (Array ℕ)) (ws : List (List ℕ)) (sz : ℕ) : Bool :=
  let c := enumOf RT ws (sz + 1)
  enumOK 240 (wsA RT ws) keyPts c && c.pts.size == sz

@[expose] def enumCheck (RT : Array (Array ℕ)) : Bool :=
  enumSize RT wS0 4096 && enumSize RT wP3 27 && enumSize RT wSa 2048 &&
    enumSize RT wPa3 9 && enumSize RT wPa5 5 && enumSize RT wSc 1024 && enumSize RT wPc 3

@[expose] def fCode (t : Array ℕ) : Array ℕ :=
  ((List.range 240).filter fun i => t[i]! == zA[i]!).toArray

@[expose] def actF (g : Array ℕ) (F : Array ℕ) : Array ℕ :=
  ((F.toList.map fun i => g[i]!).mergeSort fun a b => decide (a ≤ b)).toArray

@[expose] def validF (F : Array ℕ) : Bool :=
  F.all (· < 240) && (List.range (F.size - 1)).all fun i => decide (F[i]! < F[i + 1]!)

@[expose] def keyF (F : Array ℕ) : ℕ := F.foldl (fun acc i => acc * 240 + i) 0

@[expose] def orbF (gs : Array (Array ℕ)) (F : Array ℕ) (fuel : ℕ) : ArrCert :=
  arrBfs (fun k X => actF gs[k]! X) gs.size keyF F fuel

@[expose] def orbSize (gs : Array (Array ℕ)) (F : Array ℕ) (sz : ℕ) : Bool :=
  let c := orbF gs F (sz + 1)
  arrCertOK (fun k X => actF gs[k]! X) gs.size validF keyF F c && c.pts.size == sz

@[expose] def orbitCheck (RT : Array (Array ℕ)) : Bool :=
  validF (fCode (eA 15)) && validF (fCode (eA 3)) && validF (fCode (eA 23)) &&
  orbSize (wsA RT wX) (fCode (eA 15)) 3150 && orbSize (wsA RT wX) (fCode (eA 3)) 3780 &&
    orbSize (wsA RT wX) (fCode (eA 23)) 113400

@[expose] def inCert (c : ArrCert) (F : Array ℕ) : Bool := c.pts.toList.any (· == F)

@[expose] def subCerts (RT : Array (Array ℕ)) : List ArrCert :=
  wSub.map fun w => orbF (wsA RT wT) (actF (wA RT w) (fCode (eA 15))) 3151

@[expose] def subCheck (RT : Array (Array ℕ)) : Bool :=
  let F0 := fCode (eA 15)
  let gT := wsA RT wT
  let subs := subCerts RT
  (wSub.zip subs).all (fun p => arrCertOK (fun k X => actF gT[k]! X) gT.size validF keyF
      (actF (wA RT p.1) F0) p.2) &&
    (orbF (wsA RT wX) F0 3151).pts.toList.all (fun F =>
      F == F0 || F == actF (wA RT wG1) F0 || subs.any (inCert · F)) &&
    wSub.all (fun w => orbSize (gT.push (wA RT w)) F0 3150)

@[expose] def evenMasks : List ℕ :=
  (List.range 256).filter fun m => framePop m % 2 == 0 && m != 0 && m != 255

@[expose] def maskCheck (RT : Array (Array ℕ)) : Bool :=
  evenMasks.all (fun m => maskData.any (·.1 == m)) &&
    maskData.all fun d =>
      decide (d.2.1 < 4) && validA 240 (wA RT d.2.2) &&
        eqA 240 (conjA 240 (wA RT d.2.2) (eA d.1)) (eA (repMasks.getD d.2.1 0))

@[expose] def q8List (x y : Array ℕ) : List (Array ℕ) :=
  let x2 := compA 240 x x
  let x3 := compA 240 x2 x
  [idA 240, x, x2, x3, y, compA 240 y x, compA 240 y x2, compA 240 y x3]

@[expose] def inL (L : List (Array ℕ)) (a : Array ℕ) : Bool := L.any (eqA 240 a)

@[expose] def q8Rel (t x y : Array ℕ) : Bool :=
  eqA 240 (compA 240 x x) t && eqA 240 (compA 240 y y) t &&
    eqA 240 (conjA 240 y x) (invCand 240 x)

@[expose] def twinFail (L : List (Array ℕ)) (x y s : Array ℕ) : Bool :=
  ([x, y].any fun g => !(inL L (conjA 240 s g))) &&
    ([x, y].any fun a => [x, y].any fun b => !(commOK a (conjA 240 s b)))

@[expose] def q8Check0 (RT : Array (Array ℕ)) : Bool :=
  let t0 := eA 15
  let S0 := (enumOf RT wS0 4097).pts.toList
  let sq := S0.filter fun x => eqA 240 (compA 240 x x) t0
  let R0 := q8List (wA RT wI0) (wA RT wJ0)
  let s1 := wA RT wS1
  let R0' := R0.map (conjA 240 s1)
  let Lh := (withPairs wT).map (wA RT)
  sq.all fun x => sq.all fun y =>
    !(q8Rel t0 x y) || (inL R0 x && inL R0 y) || (inL R0' x && inL R0' y) ||
      Lh.any (twinFail (q8List x y) x y)

@[expose] def q8CheckA (RT : Array (Array ℕ)) : Bool :=
  let Sa := (enumOf RT wSa 2049).pts.toList
  let sq := Sa.filter fun x => eqA 240 (compA 240 x x) (eA 3)
  Sa.all (fun x => !(eqA 240 (compA 240 x x) (eA 252))) &&
    sq.all fun x => sq.all fun y => !(q8Rel (eA 3) x y)

@[expose] def q8CheckC (RT : Array (Array ℕ)) : Bool :=
  let Sc := (enumOf RT wSc 1025).pts.toList
  let sq := Sc.filter fun x => eqA 240 (compA 240 x x) (eA 23)
  let Lc := (withPairs wCc).map (wA RT)
  sq.all fun x => sq.all fun y => !(q8Rel (eA 23) x y) || Lc.any (twinFail (q8List x y) x y)

@[expose] def blk (u : Array ℕ) (b : ℕ) : Array ℕ := Array.ofFn (n := 240) fun i => u[b * 240 + i]!

@[expose] def actTup (g : Array ℕ) (u : Array ℕ) : Array ℕ :=
  conjA 240 g (blk u 0) ++ conjA 240 g (blk u 1) ++ conjA 240 g (blk u 2) ++ conjA 240 g (blk u 3)

@[expose] def validTup (u : Array ℕ) : Bool :=
  u.size == 960 && (List.range 4).all fun b => validA 240 (blk u b)

@[expose] def keyTup (u : Array ℕ) : ℕ :=
  ((List.range 4).flatMap fun b => keyPts.map fun p => u[b * 240 + p]!).foldl
    (fun acc i => acc * 240 + i) 0

@[expose] def tup0 (RT : Array (Array ℕ)) : Array ℕ :=
  let s1 := wA RT wS1
  wA RT wI0 ++ wA RT wJ0 ++ conjA 240 s1 (wA RT wI0) ++ conjA 240 s1 (wA RT wJ0)

@[expose] def tupleCheck (RT : Array (Array ℕ)) : Bool :=
  let gT := wsA RT wT
  let c := arrBfs (fun k u => actTup gT[k]! u) gT.size keyTup (tup0 RT) 577
  validTup (tup0 RT) &&
    arrCertOK (fun k u => actTup gT[k]! u) gT.size validTup keyTup (tup0 RT) c && c.pts.size == 576

@[expose] def letterA (K0 Lh : Array (Array ℕ)) (x : Array ℕ) (l : ℕ × ℕ) : Array ℕ :=
  if l.1 = 0 then K0[l.2]!
  else if l.1 = 1 then conjA 240 Lh[l.2]! x
  else conjA 240 Lh[l.2]! (invCand 240 x)

@[expose] def evalW (K0 Lh : Array (Array ℕ)) (x : Array ℕ) : List (ℕ × ℕ) → Array ℕ
  | [] => idA 240
  | l :: w => compA 240 (letterA K0 Lh x l) (evalW K0 Lh x w)

@[expose] def lettersOK (K0 Lh : Array (Array ℕ)) (w : List (ℕ × ℕ)) : Bool :=
  w.all fun l => decide (l.1 < 3) && decide (l.2 < (if l.1 = 0 then K0.size else Lh.size))

@[expose] def dtList (RT : Array (Array ℕ)) : Array (Array ℕ) :=
  (wDT.map fun w => conjA 240 (wA RT w) (eA 15)).toArray

@[expose] def inDT (DT : Array (Array ℕ)) (m : Std.HashMap ℕ ℕ) (d : Array ℕ) : Bool :=
  let i := (m.get? (keyA 240 keyPts d)).getD DT.size
  decide (i < DT.size) && eqA 240 d DT[i]!

@[expose] def keyMap (A : Array (Array ℕ)) : Std.HashMap ℕ ℕ :=
  (List.range A.size).foldl (fun m i => m.insert (keyA 240 keyPts A[i]!) i) ∅

@[expose] def bfsWord (K0 Lh DT : Array (Array ℕ)) (m : Std.HashMap ℕ ℕ) (x : Array ℕ)
    (fuel : ℕ) : List (ℕ × ℕ) := Id.run do
  let letters : Array (ℕ × ℕ) :=
    ((List.range K0.size).map (fun i => (0, i)) ++ (List.range Lh.size).map (fun i => (1, i))).toArray
  let gens := letters.map (letterA K0 Lh x)
  let mut pts : Array (Array ℕ) := #[idA 240]
  let mut par : Array ℕ := #[0]
  let mut lab : Array ℕ := #[0]
  let mut seen : Std.HashMap ℕ Unit := (∅ : Std.HashMap ℕ Unit).insert (keyA 240 keyPts (idA 240)) ()
  let mut i := 0
  let mut found : Option ℕ := none
  for _ in [0:fuel] do
    if found.isSome || i ≥ pts.size then break
    for k in [0:gens.size] do
      if found.isNone then
        let y := compA 240 gens[k]! pts[i]!
        let ky := keyA 240 keyPts y
        if !(seen.contains ky) then
          seen := seen.insert ky ()
          pts := pts.push y
          par := par.push i
          lab := lab.push k
          if inDT DT m y then found := some (pts.size - 1)
    i := i + 1
  match found with
  | none => return []
  | some j => Id.run do
    let mut w : List (ℕ × ℕ) := []
    let mut cur := j
    for _ in [0:fuel] do
      if cur == 0 then break
      w := w ++ [letters[lab[cur]!]!]
      cur := par[cur]!
    return w

@[expose] def simpleWord (K0 Lh DT : Array (Array ℕ)) (m : Std.HashMap ℕ ℕ) (x : Array ℕ) :
    List (ℕ × ℕ) := Id.run do
  let xi := invCand 240 x
  for k in [0:K0.size] do
    if inDT DT m (compA 240 x K0[k]!) then return [(1, 0), (0, k)]
  for h in [0:Lh.size] do
    let c1 := compA 240 x (conjA 240 Lh[h]! x)
    let c2 := compA 240 x (conjA 240 Lh[h]! xi)
    for k in [0:K0.size] do
      if inDT DT m (compA 240 c1 K0[k]!) then return [(1, 0), (1, h), (0, k)]
      if inDT DT m (compA 240 c2 K0[k]!) then return [(1, 0), (2, h), (0, k)]
  return []

@[expose] def witOK (K0 Lh DT : Array (Array ℕ)) (m : Std.HashMap ℕ ℕ) (x : Array ℕ)
    (w : List (ℕ × ℕ)) : Bool :=
  lettersOK K0 Lh w && inDT DT m (evalW K0 Lh x w)

@[expose] def k0Arr (RT : Array (Array ℕ)) : Array (Array ℕ) :=
  let s1 := wA RT wS1
  (enumBfs 240 #[wA RT wI0, wA RT wJ0, conjA 240 s1 (wA RT wI0), conjA 240 s1 (wA RT wJ0)]
    keyPts 33).pts

@[expose] def lhArr (RT : Array (Array ℕ)) : Array (Array ℕ) := ((withPairs wT).map (wA RT)).toArray

@[expose] def good2 (RT : Array (Array ℕ)) : Array (Array ℕ) :=
  let K0 := k0Arr RT
  let Lh := lhArr RT
  let DT := dtList RT
  let m := keyMap DT
  (enumOf RT wS0 4097).pts.filter fun x => !(witOK K0 Lh DT m x (simpleWord K0 Lh DT m x))

@[expose] def good3 (RT : Array (Array ℕ)) : Array (Array ℕ) :=
  let K0 := k0Arr RT
  let Lh := lhArr RT
  let DT := dtList RT
  let m := keyMap DT
  (enumOf RT wP3 28).pts.filter fun x => !(witOK K0 Lh DT m x (bfsWord K0 Lh DT m x 20000))

@[expose] def witCheck (RT : Array (Array ℕ)) : Bool :=
  let s1 := wA RT wS1
  let gK := #[wA RT wI0, wA RT wJ0, conjA 240 s1 (wA RT wI0), conjA 240 s1 (wA RT wJ0)]
  let c := enumBfs 240 gK keyPts 33
  enumOK 240 gK keyPts c && c.pts.size == 32 &&
    (dtList RT).all (fun d => !(eqA 240 d (eA 15)) && !(eqA 240 d (compA 240 (eA 15) zA))) &&
    wDT.all (fun w => validA 240 (wA RT w)) &&
    (lhArr RT).all (validA 240) &&
    (good2 RT).size ≤ 64 && (good3 RT).size ≤ 3

@[expose] def r0Check (RT : Array (Array ℕ)) : Bool :=
  let L := q8List (wA RT wI0) (wA RT wJ0)
  L.all (validA 240) && L.all (fun a => L.all fun b => inL L (compA 240 a b)) &&
    L.all fun a => inL L (invCand 240 a)

@[expose] def om1Check (_ : Unit := ()) : Bool :=
  let RT := reflTab ()
  wordsCheck RT && relCheck RT && enumCheck RT && orbitCheck RT && subCheck RT && maskCheck RT &&
    q8Check0 RT && q8CheckA RT && q8CheckC RT && tupleCheck RT && witCheck RT && r0Check RT

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om1Check
