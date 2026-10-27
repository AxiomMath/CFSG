module

public import Certificates.Data.Holder1711.Om2Data
public import Certificates.Data.Holder1711.Om1Check

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om2Check

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native
open CFSG.EvenSmallLie.OmegaEight CFSG.EvenSmallLie.OmegaEight.Weyl
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om2Data
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om1Check
  (reflTab wA wordOK inL commOK withPairs keyF validF letterA evalW lettersOK eA)

@[expose] def pairA (a b : Array ℕ) : Array ℕ := a ++ b.map (· + 240)

@[expose] def genY (RT : Array (Array ℕ)) : Array (Array ℕ) :=
  ((List.range 8).map fun i => pairA (wA RT (omWords.getD i [])) (wA RT (yW.getD i []))).toArray

@[expose] def lettersY (RT : Array (Array ℕ)) : Array (Array ℕ) :=
  genY RT ++ (genY RT).map (invCand 480)

@[expose] def wY (LY : Array (Array ℕ)) : List ℕ → Array ℕ
  | [] => idA 480
  | l :: w => compA 480 LY[l]! (wY LY w)

@[expose] def wordYOK (w : List ℕ) : Bool := w.all (· < 16)

@[expose] def cA (k : ℕ) : Array ℕ :=
  if k = 0 then pairA negArr (idA 240) else if k = 1 then pairA (idA 240) negArr
  else pairA negArr negArr

@[expose] def fstA (a : Array ℕ) : Array ℕ := a.extract 0 240

@[expose] def sndA (a : Array ℕ) : Array ℕ := (a.extract 240 480).map (· - 240)

@[expose] def keyPtsY : List ℕ := keyPts ++ keyPts.map (· + 240)

@[expose] def commY (x y : Array ℕ) : Bool := eqA 480 (compA 480 x y) (compA 480 y x)

@[expose] def res120 (a : Array ℕ) : Array ℕ := Array.ofFn (n := 120) fun j => a[(j : ℕ)]!

@[expose] def genCheck (RT : Array (Array ℕ)) : Bool :=
  yW.length == 8 && yW.all (fun w => wordOK w && validA 240 (wA RT w)) &&
    (List.range 8).all fun i =>
      eqA 120 (res120 (conjA 360 genArrs[8]! genArrs[i]!)) (pArr (wA RT (yW.getD i [])))

@[expose] def allWordsY : List (List ℕ) :=
  [wT0, wI0, wJ0, wTc, wFuseC, wLiftA, wLiftB] ++ wFuse0 ++ wS0 ++ wP3 ++ wSc ++ wPc ++ wSub ++
    wDT ++ wCR

@[expose] def wordsCheckY (RT : Array (Array ℕ)) : Bool :=
  (genY RT).all (validA 480) && wFuse0.length == 3 &&
    allWordsY.all fun w => wordYOK w && validA 480 (wY (lettersY RT) w)

@[expose] def q8ListY (x y : Array ℕ) : List (Array ℕ) :=
  let x2 := compA 480 x x
  let x3 := compA 480 x2 x
  [idA 480, x, x2, x3, y, compA 480 y x, compA 480 y x2, compA 480 y x3]

@[expose] def inLY (L : List (Array ℕ)) (a : Array ℕ) : Bool := L.any (eqA 480 a)

@[expose] def q8RelY (t x y : Array ℕ) : Bool :=
  eqA 480 (compA 480 x x) t && eqA 480 (compA 480 y y) t &&
    eqA 480 (conjA 480 y x) (invCand 480 x)

@[expose] def wT : List (List ℕ) := wS0 ++ wP3

@[expose] def wCc : List (List ℕ) := wSc ++ wPc

@[expose] def relCheckY (RT : Array (Array ℕ)) : Bool :=
  let LY := lettersY RT
  let t0 := wY LY wT0
  let i0 := wY LY wI0
  let j0 := wY LY wJ0
  let tc := wY LY wTc
  let R0 := q8ListY i0 j0
  eqA 240 (fstA t0) (eA 15) && eqA 480 (compA 480 t0 t0) (idA 480) &&
    q8RelY t0 i0 j0 &&
    (List.range 3).all (fun k => eqA 480 (conjA 480 (wY LY (wFuse0.getD k [])) t0)
      (compA 480 t0 (cA k))) &&
    wT.all (fun w => commY (wY LY w) t0 && inLY R0 (conjA 480 (wY LY w) i0) &&
      inLY R0 (conjA 480 (wY LY w) j0)) &&
    eqA 240 (fstA tc) (eA 23) && eqA 480 (compA 480 tc tc) (idA 480) &&
    eqA 480 (conjA 480 (wY LY wFuseC) tc) (compA 480 tc (cA 1)) &&
    wCc.all (fun w => commY (wY LY w) tc) &&
    eqA 240 (fstA (wY LY wLiftA)) (eA 3) && eqA 240 (fstA (wY LY wLiftB)) (eA 252) &&
    [wLiftA, wLiftB].all (fun w =>
      !(eqA 480 (compA 480 (wY LY w) (wY LY w)) (idA 480)) &&
      !(eqA 480 (compA 480 (compA 480 (wY LY w) (cA 1)) (compA 480 (wY LY w) (cA 1)))
        (idA 480))) &&
    wCR.all (fun w => commY (wY LY w) i0 && commY (wY LY w) j0)

@[expose] def enumOfY (LY : Array (Array ℕ)) (ws : List (List ℕ)) (fuel : ℕ) : ArrCert :=
  enumBfs 480 (ws.map (wY LY)).toArray keyPtsY fuel

@[expose] def enumSizeY (LY : Array (Array ℕ)) (ws : List (List ℕ)) (sz : ℕ) : Bool :=
  let c := enumOfY LY ws (sz + 1)
  enumOK 480 (ws.map (wY LY)).toArray keyPtsY c && c.pts.size == sz

@[expose] def enumCheckY (RT : Array (Array ℕ)) : Bool :=
  let LY := lettersY RT
  enumSizeY LY wS0 4096 && enumSizeY LY wP3 27 && enumSizeY LY wSc 1024 &&
    enumSizeY LY wPc 3 && enumSizeY LY wCR 4608

@[expose] def fCodeY (t : Array ℕ) : Array ℕ :=
  ((List.range 480).filter fun i => t[i]! == (cA 2)[i]!).toArray

@[expose] def actFY (g : Array ℕ) (F : Array ℕ) : Array ℕ :=
  ((F.toList.map fun i => g[i]!).mergeSort fun a b => decide (a ≤ b)).toArray

@[expose] def validFY (F : Array ℕ) : Bool :=
  F.all (· < 480) && (List.range (F.size - 1)).all fun i => decide (F[i]! < F[i + 1]!)

@[expose] def orbFY (gs : Array (Array ℕ)) (F : Array ℕ) (fuel : ℕ) : ArrCert :=
  arrBfs (fun k X => actFY gs[k]! X) gs.size keyF F fuel

@[expose] def orbSizeY (gs : Array (Array ℕ)) (F : Array ℕ) (sz : ℕ) : Bool :=
  let c := orbFY gs F (sz + 1)
  arrCertOK (fun k X => actFY gs[k]! X) gs.size validFY keyF F c && c.pts.size == sz

@[expose] def orbitCheckY (RT : Array (Array ℕ)) : Bool :=
  let LY := lettersY RT
  validFY (fCodeY (wY LY wT0)) && orbSizeY (genY RT) (fCodeY (wY LY wT0)) 6300

@[expose] def inCertY (c : ArrCert) (F : Array ℕ) : Bool := c.pts.toList.any (· == F)

@[expose] def subCertsY (RT : Array (Array ℕ)) : List ArrCert :=
  let LY := lettersY RT
  wSub.map fun w => orbFY (wT.map (wY LY)).toArray (actFY (wY LY w) (fCodeY (wY LY wT0))) 6301

@[expose] def subCheckY (RT : Array (Array ℕ)) : Bool :=
  let LY := lettersY RT
  let F0 := fCodeY (wY LY wT0)
  let gT := (wT.map (wY LY)).toArray
  let subs := subCertsY RT
  (wSub.zip subs).all (fun p => arrCertOK (fun k X => actFY gT[k]! X) gT.size validFY keyF
      (actFY (wY LY p.1) F0) p.2) &&
    (orbFY (genY RT) F0 6301).pts.toList.all (fun F =>
      F == F0 || wFuse0.any (fun w => F == actFY (wY LY w) F0) || subs.any (inCertY · F)) &&
    wSub.all (fun w => orbSizeY (gT.push (wY LY w)) F0 6300)

@[expose] def twinFailY (L : List (Array ℕ)) (x y s : Array ℕ) : Bool :=
  ([x, y].any fun g => !(inLY L (conjA 480 s g))) &&
    ([x, y].any fun a => [x, y].any fun b => !(commY a (conjA 480 s b)))

@[expose] def q8Check0Y (RT : Array (Array ℕ)) : Bool :=
  let LY := lettersY RT
  let t0 := wY LY wT0
  let S0 := (enumOfY LY wS0 4097).pts.toList
  let sq := S0.filter fun x => eqA 480 (compA 480 x x) t0
  let R0 := q8ListY (wY LY wI0) (wY LY wJ0)
  let Lh := (withPairs wT).map (wY LY)
  sq.all fun x => sq.all fun y =>
    !(q8RelY t0 x y) || (inLY R0 x && inLY R0 y) || Lh.any (twinFailY (q8ListY x y) x y)

@[expose] def q8CheckCY (RT : Array (Array ℕ)) : Bool :=
  let LY := lettersY RT
  let tc := wY LY wTc
  let Sc := (enumOfY LY wSc 1025).pts.toList
  let sq := Sc.filter fun x => eqA 480 (compA 480 x x) tc
  let Lc := (withPairs wCc).map (wY LY)
  sq.all fun x => sq.all fun y => !(q8RelY tc x y) || Lc.any (twinFailY (q8ListY x y) x y)

@[expose] def blkY (u : Array ℕ) (b : ℕ) : Array ℕ := Array.ofFn (n := 480) fun i => u[b * 480 + i]!

@[expose] def actTupY (m : ℕ) (g : Array ℕ) (u : Array ℕ) : Array ℕ :=
  (List.range m).foldl (fun acc b => acc ++ conjA 480 g (blkY u b)) #[]

@[expose] def validTupY (m : ℕ) (u : Array ℕ) : Bool :=
  u.size == m * 480 && (List.range m).all fun b => validA 480 (blkY u b)

@[expose] def keyTupY (m : ℕ) (u : Array ℕ) : ℕ :=
  ((List.range m).flatMap fun b => keyPtsY.map fun p => u[b * 480 + p]!).foldl
    (fun acc i => acc * 480 + i) 0

@[expose] def tupSize (m : ℕ) (gs : Array (Array ℕ)) (u0 : Array ℕ) (sz : ℕ) : Bool :=
  let c := arrBfs (fun k u => actTupY m gs[k]! u) gs.size (keyTupY m) u0 (sz + 1)
  validTupY m u0 && arrCertOK (fun k u => actTupY m gs[k]! u) gs.size (validTupY m) (keyTupY m)
    u0 c && c.pts.size == sz

@[expose] def tup2 (LY : Array (Array ℕ)) : Array ℕ := wY LY wI0 ++ wY LY wJ0

@[expose] def tup8 (LY : Array (Array ℕ)) : Array ℕ :=
  ([[]] ++ wFuse0).foldl (fun acc w =>
    acc ++ conjA 480 (wY LY w) (wY LY wI0) ++ conjA 480 (wY LY w) (wY LY wJ0)) #[]

@[expose] def tupleCheckY (RT : Array (Array ℕ)) : Bool :=
  let LY := lettersY RT
  tupSize 2 (wT.map (wY LY)).toArray (tup2 LY) 24 &&
    tupSize 8 (wCR.map (wY LY)).toArray (tup8 LY) 576

@[expose] def inDTY (DT : Array (Array ℕ)) (m : Std.HashMap ℕ ℕ) (d : Array ℕ) : Bool :=
  let i := (m.get? (keyA 480 keyPtsY d)).getD DT.size
  decide (i < DT.size) && eqA 480 d DT[i]!

@[expose] def keyMapY (A : Array (Array ℕ)) : Std.HashMap ℕ ℕ :=
  (List.range A.size).foldl (fun m i => m.insert (keyA 480 keyPtsY A[i]!) i) ∅

@[expose] def letterY (K0 Lh : Array (Array ℕ)) (x : Array ℕ) (l : ℕ × ℕ) : Array ℕ :=
  if l.1 = 0 then K0[l.2]!
  else if l.1 = 1 then conjA 480 Lh[l.2]! x
  else conjA 480 Lh[l.2]! (invCand 480 x)

@[expose] def evalWY (K0 Lh : Array (Array ℕ)) (x : Array ℕ) : List (ℕ × ℕ) → Array ℕ
  | [] => idA 480
  | l :: w => compA 480 (letterY K0 Lh x l) (evalWY K0 Lh x w)

@[expose] def simpleWordY (K0 Lh DT : Array (Array ℕ)) (m : Std.HashMap ℕ ℕ) (x : Array ℕ) :
    List (ℕ × ℕ) := Id.run do
  let xi := invCand 480 x
  for k in [0:K0.size] do
    if inDTY DT m (compA 480 x K0[k]!) then return [(1, 0), (0, k)]
  for h in [0:Lh.size] do
    let c1 := compA 480 x (conjA 480 Lh[h]! x)
    let c2 := compA 480 x (conjA 480 Lh[h]! xi)
    for k in [0:K0.size] do
      if inDTY DT m (compA 480 c1 K0[k]!) then return [(1, 0), (1, h), (0, k)]
      if inDTY DT m (compA 480 c2 K0[k]!) then return [(1, 0), (2, h), (0, k)]
  return []

@[expose] def bfsWordY (K0 Lh DT : Array (Array ℕ)) (m : Std.HashMap ℕ ℕ) (x : Array ℕ)
    (fuel : ℕ) : List (ℕ × ℕ) := Id.run do
  let letters : Array (ℕ × ℕ) :=
    ((List.range K0.size).map (fun i => (0, i)) ++ (List.range Lh.size).map (fun i => (1, i))).toArray
  let gens := letters.map (letterY K0 Lh x)
  let mut pts : Array (Array ℕ) := #[idA 480]
  let mut par : Array ℕ := #[0]
  let mut lab : Array ℕ := #[0]
  let mut seen : Std.HashMap ℕ Unit :=
    (∅ : Std.HashMap ℕ Unit).insert (keyA 480 keyPtsY (idA 480)) ()
  let mut i := 0
  let mut found : Option ℕ := none
  for _ in [0:fuel] do
    if found.isSome || i ≥ pts.size then break
    for k in [0:gens.size] do
      if found.isNone then
        let y := compA 480 gens[k]! pts[i]!
        let ky := keyA 480 keyPtsY y
        if !(seen.contains ky) then
          seen := seen.insert ky ()
          pts := pts.push y
          par := par.push i
          lab := lab.push k
          if inDTY DT m y then found := some (pts.size - 1)
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

@[expose] def lettersOKY (K0 Lh : Array (Array ℕ)) (w : List (ℕ × ℕ)) : Bool :=
  w.all fun l => decide (l.1 < 3) && decide (l.2 < (if l.1 = 0 then K0.size else Lh.size))

@[expose] def witOKY (K0 Lh DT : Array (Array ℕ)) (m : Std.HashMap ℕ ℕ) (x : Array ℕ)
    (w : List (ℕ × ℕ)) : Bool :=
  lettersOKY K0 Lh w && inDTY DT m (evalWY K0 Lh x w)

@[expose] def k0ArrY (LY : Array (Array ℕ)) : Array (Array ℕ) := (q8ListY (wY LY wI0) (wY LY wJ0)).toArray

@[expose] def lhArrY (LY : Array (Array ℕ)) : Array (Array ℕ) := ((withPairs wT).map (wY LY)).toArray

@[expose] def dtListY (LY : Array (Array ℕ)) (Zt : List (Array ℕ)) : Array (Array ℕ) :=
  ((wDT.map fun w => conjA 480 (wY LY w) (wY LY wT0)).filter fun d => !(inLY Zt d)).toArray

@[expose] def good2Y (RT : Array (Array ℕ)) (Zt : List (Array ℕ)) : Array (Array ℕ) :=
  let LY := lettersY RT
  let K0 := k0ArrY LY
  let Lh := lhArrY LY
  let DT := dtListY LY Zt
  let m := keyMapY DT
  (enumOfY LY wS0 4097).pts.filter fun x => !(witOKY K0 Lh DT m x (simpleWordY K0 Lh DT m x))

@[expose] def good3Y (RT : Array (Array ℕ)) (Zt : List (Array ℕ)) : Array (Array ℕ) :=
  let LY := lettersY RT
  let K0 := k0ArrY LY
  let Lh := lhArrY LY
  let DT := dtListY LY Zt
  let m := keyMapY DT
  (enumOfY LY wP3 28).pts.filter fun x => !(witOKY K0 Lh DT m x (bfsWordY K0 Lh DT m x 40000))

@[expose] def zt1 (LY : Array (Array ℕ)) : List (Array ℕ) := [wY LY wT0]

@[expose] def zt4 (LY : Array (Array ℕ)) : List (Array ℕ) :=
  wY LY wT0 :: (List.range 3).map fun k => compA 480 (wY LY wT0) (cA k)

@[expose] def witCheckY (RT : Array (Array ℕ)) : Bool :=
  let LY := lettersY RT
  (k0ArrY LY).all (validA 480) && (lhArrY LY).all (validA 480) &&
    (good2Y RT (zt1 LY)).size ≤ 8 && (good3Y RT (zt1 LY)).size ≤ 1 &&
    (good2Y RT (zt4 LY)).size ≤ 1184 && (good3Y RT (zt4 LY)).size ≤ 19

@[expose] def treeArrs (gs : Array (Array ℕ)) (c : ArrCert) : Array (Array ℕ) := Id.run do
  let mut tw : Array (Array ℕ) := #[idA 480]
  for i in [1:c.pts.size] do
    tw := tw.push (compA 480 gs[c.lab[i]!]! tw[c.par[i]!]!)
  return tw

@[expose] def pairCheck (RT : Array (Array ℕ)) : Bool :=
  let LY := lettersY RT
  let t0 := wY LY wT0
  let i0 := wY LY wI0
  let j0 := wY LY wJ0
  let c := orbFY (genY RT) (fCodeY t0) 6301
  let tw := treeArrs (genY RT) c
  let idx : Std.HashMap ℕ ℕ :=
    (List.range c.pts.size).foldl (fun m i => m.insert (keyF c.pts[i]!) i) ∅
  let CR := (enumOfY LY wCR 4609).pts
  wFuse0.all (fun w => let f := wY LY w
    commY (conjA 480 f i0) i0 && commY (conjA 480 f i0) j0 &&
      commY (conjA 480 f j0) i0 && commY (conjA 480 f j0) j0) &&
  CR.all fun u =>
    !(eqA 480 (compA 480 u u) (idA 480)) ||
      (let F := fCodeY u
       let i := (idx.get? (keyF F)).getD c.pts.size
       !(decide (i < c.pts.size) && c.pts[i]! == F) ||
         (let g := tw[i]!
          eqA 480 (conjA 480 g t0) u &&
            (!(commY (conjA 480 g i0) i0 && commY (conjA 480 g i0) j0 &&
                commY (conjA 480 g j0) i0 && commY (conjA 480 g j0) j0) ||
              inLY (zt4 LY) u)))

@[expose] def r0CheckY (RT : Array (Array ℕ)) : Bool :=
  let LY := lettersY RT
  let L := q8ListY (wY LY wI0) (wY LY wJ0)
  L.all (validA 480) && L.all (fun a => L.all fun b => inLY L (compA 480 a b)) &&
    L.all fun a => inLY L (invCand 480 a)

@[expose] def om2CheckA (_ : Unit := ()) : Bool :=
  let RT := reflTab ()
  genCheck RT && wordsCheckY RT && relCheckY RT && enumCheckY RT && orbitCheckY RT &&
    subCheckY RT && r0CheckY RT

@[expose] def om2CheckB (_ : Unit := ()) : Bool :=
  let RT := reflTab ()
  q8Check0Y RT && q8CheckCY RT && tupleCheckY RT && witCheckY RT && pairCheck RT

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om2Check
