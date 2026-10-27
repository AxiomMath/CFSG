module

public import Certificates.Data.SuzLevelTwoPins
public import Certificates.Data.SuzModelGroupsInputs
public import CFSG.Sporadic.SuzRecog.Q3ACheck
public import CFSG.Sporadic.SuzRecog.LevelTwoHomotopy
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3B0SuzTests

public section

namespace CFSG.Sporadic.SuzRecog.LevelTwo

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Sporadic.SuzRecog.LevelTwoData
  CFSG.Sporadic.SuzRecog.ElimCert

@[expose] def conjA (g gi a : Array Nat) : Array Nat := compA 1782 g (compA 1782 a gi)

@[expose] def conjEq (g gi a b : Array Nat) : Bool := eqA 1782 b (compA 1782 g (compA 1782 a gi))

@[expose] def t1Arr : Array Nat := CFSG.Sporadic.SuzOddCore.invRepArr 1

@[expose] def rhoInv : Array Nat := invCand 1782 rhoArr

@[expose] def gens : Array (Array Nat) := #[xStrong 0, xStrong 1]

@[expose] def gensInv : Array (Array Nat) := gens.map (invCand 1782)

@[expose] def xLevels : Array Level := rawLevels 1782 xStrongArrs xBase.toArray

@[expose] def memX (g : Array Nat) : Bool := siftA 1782 xLevels xBase.toArray 0 g

@[expose] def commA (g h : Array Nat) : Bool := eqA 1782 (compA 1782 g h) (compA 1782 h g)

@[expose] def rhoConj (w : Array Nat) : Array Nat := conjA rhoArr rhoInv w

@[expose] def fp (a : Array Nat) : Nat :=
  a[17]! + 1782 * (a[333]! + 1782 * (a[901]! + 1782 * (a[1500]! + 1782 * (a[1234]! +
    1782 * a[77]!))))

@[expose] def fpConj (g gi a : Array Nat) : Nat :=
  let e := fun i => g[a[gi[i]!]!]!
  e 17 + 1782 * (e 333 + 1782 * (e 901 + 1782 * (e 1500 + 1782 * (e 1234 + 1782 * e 77))))

@[expose] def fpTable (L : Array (Array Nat)) : Std.HashMap Nat Nat := Id.run do
  let mut m : Std.HashMap Nat Nat := ∅
  for i in [0:L.size] do
    m := m.insert (fp L[i]!) i
  return m

@[expose] def aSearch : Array (Array Nat) × Array Nat × Array Nat × Array (Array Nat) := Id.run do
  let mut pts : Array (Array Nat) := #[t1Arr]
  let mut par : Array Nat := #[0]
  let mut lab : Array Nat := #[0]
  let mut tr : Array (Array Nat) := #[idA 1782]
  let mut idx : Std.HashSet Nat := (∅ : Std.HashSet Nat).insert (fp t1Arr)
  for h in [0:2835] do
    if h < pts.size then
      for s in [0:2] do
        let f := fpConj gens[s]! gensInv[s]! pts[h]!
        if !idx.contains f then
          idx := idx.insert f
          pts := pts.push (conjA gens[s]! gensInv[s]! pts[h]!)
          par := par.push h
          lab := lab.push s
          tr := tr.push (compA 1782 gens[s]! tr[h]!)
  return (pts, par, lab, tr)

@[expose] def aPar : Array Nat := hexTable 3 2835 0 LevelTwoPins.aTreeHex

@[expose] def aLab : Array Nat := hexTable 3 2835 2835 LevelTwoPins.aTreeHex

@[expose] def aAt (i : Nat) : Array Nat :=
  if _h : 0 < i ∧ aPar[i]! < i then conjA gens[aLab[i]!]! gensInv[aLab[i]!]! (aAt aPar[i]!)
  else t1Arr
termination_by i
decreasing_by exact _h.2

@[expose] def aPts : Array (Array Nat) := (Array.range 2835).map aAt

@[expose] def aIdx : Std.HashMap Nat Nat := fpTable aPts

@[expose] def tripOf (w : Array Nat) : Array (Array Nat) := #[w, rhoConj w, rhoConj (rhoConj w)]

@[expose] def wPar : Array Nat := hexTable 3 162 0 LevelTwoPins.wTreeHex

@[expose] def wLab : Array Nat := hexTable 3 162 162 LevelTwoPins.wTreeHex

@[expose] def wAt (j : Nat) : Array Nat :=
  if _h : 0 < j ∧ wPar[j]! < j then conjA gens[wLab[j]!]! gensInv[wLab[j]!]! (wAt wPar[j]!)
  else w0Arr
termination_by j
decreasing_by exact _h.2

@[expose] def wPts : Array (Array Nat) := (Array.range 162).map wAt

@[expose] def trips : Array (Array (Array Nat)) := wPts.map tripOf

@[expose] def trip (j : Nat) : Array (Array Nat) := trips[j]!

@[expose] def vIdx : Std.HashMap Nat Nat := Id.run do
  let mut m : Std.HashMap Nat Nat := ∅
  for j in [0:wPts.size] do
    for z in trip j do
      m := m.insert (fp z) j
  return m

@[expose] def actV (g gi : Array Nat) (v : Nat) : Nat :=
  if v < 2835 then aIdx.getD (fpConj g gi aPts[v]!) 2835
  else 2835 + vIdx.getD (fpConj g gi wPts[v - 2835]!) 162

@[expose] def sendsB (g gi : Array Nat) (v v' : Nat) : Bool :=
  if v < 2835 then v' < 2835 && conjEq g gi aPts[v]! aPts[v']!
  else 2835 ≤ v' && v' < 2997 &&
    (conjEq g gi wPts[v - 2835]! (trip (v' - 2835))[0]! ||
      conjEq g gi wPts[v - 2835]! (trip (v' - 2835))[1]! ||
      conjEq g gi wPts[v - 2835]! (trip (v' - 2835))[2]!)

@[expose] def vtabs : Array (Array Nat) :=
  Array.ofFn (n := 2) fun s =>
    Array.ofFn (n := 2997) fun v => actV gens[s.val]! gensInv[s.val]! v.val

@[expose] def vtab (s : Nat) : Array Nat := vtabs[s]!

@[expose] def q1Fp : Std.HashSet Nat := Id.run do
  let mut m : Std.HashSet Nat := ∅
  for v in [0:64] do
    let p := CFSG.ComponentClassification.AS81.SuzB0.qProd v
    m := m.insert (fp p)
    m := m.insert (fp (compA 1782 p t1Arr))
  return m

@[expose] def o8Base : Array Nat :=
  ((List.range 2835).filter fun i => i != 0 && q1Fp.contains (fp aPts[i]!)).toArray

@[expose] def vBase : Array Nat :=
  ((List.range 162).filter fun j => commA t1Arr wPts[j]!).toArray.map (2835 + ·)

@[expose] def nbrA : Array (Array Nat) :=
  let e := hexTable 3 102060 0 LevelTwoPins.nbrHex
  Array.ofFn (n := 2835) fun i => Array.ofFn (n := 36) fun k => e[36 * i.val + k.val]!

@[expose] def nbr : Array (Array Nat) :=
  Array.ofFn (n := 2997) fun v => if v.val < 2835 then nbrA[v.val]! else #[]

@[expose] def triB (x y z : Nat) : Bool :=
  adjB nbr x y && adjB nbr y z && adjB nbr x z &&
    ((if 2835 ≤ x then 1 else 0) + (if 2835 ≤ y then 1 else 0) + (if 2835 ≤ z then 1 else 0) == 1)

@[expose] def posIn (x y : Nat) : Nat := ((nbr[x]!).findIdx? (· == y)).getD 36

@[expose] def eid (x y : Nat) : Nat :=
  if x < 2835 && (y ≥ 2835 || x < y) then x * 36 + posIn x y else y * 36 + posIn y x

@[expose] def incT : Array Bool := Id.run do
  let mut out : Array Bool := Array.replicate (2835 * 162) false
  for i in [0:2835] do
    for y in nbrA[i]! do
      if 2835 ≤ y then out := out.set! (i * 162 + (y - 2835)) true
  return out

@[expose] def treePar : Array Nat := hexTable 3 2997 0 LevelTwoPins.spanHex

@[expose] def treeDep : Array Nat := hexTable 3 2997 2997 LevelTwoPins.spanHex

@[expose] def cells : Array (Nat × Nat × Nat) × Array (Nat × Nat × Nat) := Id.run do
  let mut out : Array (Nat × Nat × Nat) := #[]
  let mut ids : Array (Nat × Nat × Nat) := #[]
  for x in [0:2835] do
    for y in nbrA[x]! do
      if x < y && y < 2835 then
        for z in nbrA[x]! do
          if 2835 ≤ z && incT[y * 162 + (z - 2835)]! then
            out := out.push (x, y, z)
            ids := ids.push (eid x y, eid x z, eid y z)
  return (out, ids)

@[expose] def elimCore (cs ids : Array (Nat × Nat × Nat)) (par tids : Array Nat) :
    Array (Array Nat) × Array Nat := Id.run do
  let ne := 2835 * 36
  let mut steps : Array (Array Nat) := #[]
  let mut stepOf : Array Nat := Array.replicate ne 0
  let mut done : Array Bool := Array.replicate ne false
  for z in [1:2997] do
    let e := tids[z]!
    stepOf := stepOf.set! e steps.size
    done := done.set! e true
    steps := steps.push #[par[z]!, z]
  let mut ecells : Array (Array Nat) := Array.replicate ne #[]
  for c in [0:cs.size] do
    let (e₁, e₂, e₃) := ids[c]!
    ecells := ecells.modify e₁ (·.push c)
    ecells := ecells.modify e₂ (·.push c)
    ecells := ecells.modify e₃ (·.push c)
  let mut queue : Array Nat := #[]
  for c in [0:cs.size] do
    let (e₁, e₂, e₃) := ids[c]!
    if (if done[e₁]! then 0 else 1) + (if done[e₂]! then 0 else 1) +
        (if done[e₃]! then 0 else 1) == 1 then
      queue := queue.push c
  for h in [0:4 * cs.size] do
    if h < queue.size then
      let c := queue[h]!
      let (e₁, e₂, e₃) := ids[c]!
      if (if done[e₁]! then 0 else 1) + (if done[e₂]! then 0 else 1) +
          (if done[e₃]! then 0 else 1) == 1 then
        let (a, b, v) := cs[c]!
        let (x, z, y, e, f₁, f₂) := if !done[e₁]! then (a, b, v, e₁, e₂, e₃)
          else if !done[e₂]! then (a, v, b, e₂, e₁, e₃) else (b, v, a, e₃, e₁, e₂)
        stepOf := stepOf.set! e steps.size
        done := done.set! e true
        steps := steps.push #[x, z, y, stepOf[f₁]!, stepOf[f₂]!]
        for c' in ecells[e]! do
          let (d₁, d₂, d₃) := ids[c']!
          if (if done[d₁]! then 0 else 1) + (if done[d₂]! then 0 else 1) +
              (if done[d₃]! then 0 else 1) == 1 then
            queue := queue.push c'
  return (steps, stepOf)

@[expose] def elimSteps : Array (Array Nat) :=
  let v := hexTable 3 220647 0 LevelTwoPins.stepVHex
  let e := hexTable 5 147098 0 LevelTwoPins.stepIHex
  Array.ofFn (n := 76545) fun i =>
    if i.val < 2996 then #[treePar[i.val + 1]!, i.val + 1]
    else
      let j := i.val - 2996
      #[v[3 * j]!, v[3 * j + 1]!, v[3 * j + 2]!, e[2 * j]!, e[2 * j + 1]!]

@[expose] def elimEmap : Array (Array Nat) :=
  let e := hexTable 5 102060 0 LevelTwoPins.emapHex
  Array.ofFn (n := 2997) fun x =>
    if x.val < 2835 then Array.ofFn (n := 36) fun k => e[36 * x.val + k.val]! else #[]

abbrev Elt : Type := Array Nat × Array Nat

@[expose] def eltOne : Elt := (idA 1782, idA 1782)

@[expose] def orbitElems (gs : Array Elt) (b : Nat) : Std.HashMap Nat Elt := Id.run do
  let mut el : Std.HashMap Nat Elt := (∅ : Std.HashMap Nat Elt).insert b eltOne
  let mut queue : Array Nat := #[b]
  for h in [0:2997] do
    if h < queue.size then
      let x := queue[h]!
      let (e, ei) := el.getD x eltOne
      for k in [0:gs.size] do
        let (g, gi) := gs[k]!
        let y := actV g gi x
        if !el.contains y then
          el := el.insert y (compA 1782 g e, compA 1782 ei gi)
          queue := queue.push y
  return el

@[expose] def eltPin (k : Nat) : Elt :=
  let e := hexTable 3 1782 (1782 * k) LevelTwoPins.eltHex
  (e, invCand 1782 e)

@[expose] def genP : Array Elt := Array.ofFn (n := 6) fun k => eltPin k.val

@[expose] def genQ : Array Elt := Array.ofFn (n := 6) fun k => eltPin (6 + k.val)

@[expose] def p1 : Nat := o8Base[0]!

@[expose] def elPq : Std.HashMap Nat Elt := orbitElems genP 2835

@[expose] def elQp : Std.HashMap Nat Elt := orbitElems genQ 0

@[expose] def cellReps : Array Nat := #[2852, 2890, 2922, 2970]

@[expose] def swapE : Elt := eltPin 12

@[expose] def cellC (k : Nat) : Elt := eltPin (13 + k)

@[expose] def cellC' (k : Nat) : Elt := eltPin (17 + k)

@[expose] def nbPPar : Array Nat := hexTable 3 36 0 LevelTwoPins.nbPHex

@[expose] def nbPLab : Array Nat := hexTable 3 36 36 LevelTwoPins.nbPHex

@[expose] def nbPDep : Array Nat := hexTable 3 36 72 LevelTwoPins.nbPHex

@[expose] def nbQ : Array Nat := hexTable 3 315 0 LevelTwoPins.nbQHex

@[expose] def nbQPar : Array Nat := hexTable 3 315 315 LevelTwoPins.nbQHex

@[expose] def nbQLab : Array Nat := hexTable 3 315 630 LevelTwoPins.nbQHex

@[expose] def nbQDep : Array Nat := hexTable 3 315 945 LevelTwoPins.nbQHex

@[expose] def triY1 : Array Nat := hexTable 3 180 0 LevelTwoPins.triHex

@[expose] def triY2 : Array Nat := hexTable 3 180 180 LevelTwoPins.triHex

@[expose] def triPar : Array Nat := hexTable 3 180 360 LevelTwoPins.triHex

@[expose] def triLab : Array Nat := hexTable 3 180 540 LevelTwoPins.triHex

@[expose] def triIdx : Array Nat := hexTable 3 324 0 LevelTwoPins.triIdxHex

@[expose] def bArr : Array Nat := compA 1782 t1Arr aPts[p1]!

@[expose] def bIdx : Nat := aIdx.getD (fp bArr) 2835

@[expose] def elemOK (g gi : Array Nat) : Bool := isInvA 1782 g gi && memX g

@[expose] def chainOK : Bool :=
  xStrongArrs.size == 9 &&
    rawChainOK 1782 gens xStrongArrs xBase.toArray xWords 4 &&
    rawOrbitSizes 1782 xStrongArrs xBase.toArray == [162, 105, 64, 3, 3]

@[expose] def basicOK : Bool :=
  isInvA 1782 rhoArr rhoInv &&
    eqA 1782 (compA 1782 rhoArr (compA 1782 rhoArr rhoArr)) (idA 1782) &&
    !eqA 1782 rhoArr (idA 1782) && memX rhoArr &&
    allLt 2 (fun s => isInvA 1782 gens[s]! gensInv[s]! && commA gens[s]! rhoArr &&
      CFSG.Sporadic.SuzOddCore.inM gens[s]!) &&
    isInvA 1782 t1Arr t1Arr && memX t1Arr &&
    isInvA 1782 w0Arr w0Arr && commA w0Arr t1Arr && commA w0Arr (rhoConj w0Arr) &&
    !eqA 1782 w0Arr (rhoConj w0Arr)

@[expose] def aOK : Bool :=
  aPts.size == 2835 && eqA 1782 aPts[0]! t1Arr &&
    allLt 2835 (fun i => isInvA 1782 aPts[i]! aPts[i]! && aIdx.getD (fp aPts[i]!) 2835 == i) &&
    allLt 2 (fun s => allLt 2835 fun i => sendsB gens[s]! gensInv[s]! i (vtab s)[i]!)

@[expose] def vOK : Bool :=
  wPts.size == 162 && eqA 1782 wPts[0]! w0Arr &&
    allLt 162 (fun j => isInvA 1782 wPts[j]! wPts[j]! && !eqA 1782 (trip j)[0]! (trip j)[1]! &&
      allLt 3 fun k => vIdx.getD (fp (trip j)[k]!) 162 == j) &&
    allLt 2 (fun s => allLt 162 fun j =>
      sendsB gens[s]! gensInv[s]! (2835 + j) (vtab s)[2835 + j]!)

@[expose] def graphOK : Bool :=
  nbr.size == 2997 &&
    allLt 2 fun s => allLt 2997 fun x => (nbr[x]!).all fun y => adjB nbr (vtab s)[x]! (vtab s)[y]!

@[expose] def elimOK : Bool := ok 2997 nbr treePar treeDep triB elimSteps elimEmap

@[expose] def pElemOK (e : Elt) (v v' : Nat) : Bool :=
  elemOK e.1 e.2 && sendsB e.1 e.2 0 0 && sendsB e.1 e.2 v v'

@[expose] def nbPOK : Bool :=
  let n₀ := nbr[0]!
  allLt 6 (fun l => elemOK genP[l]!.1 genP[l]!.2 && sendsB genP[l]!.1 genP[l]!.2 0 0) &&
    n₀.size == 36 && n₀[0]! == p1 && n₀[18]! == 2835 &&
    allLt 2997 (fun y => !adjB nbr 0 y || occB n₀ y) &&
    allLt 36 (fun k => (decide (k < 18) == decide (n₀[k]! < 2835)) &&
      (k == 0 || k == 18 ||
        (nbPPar[k]! < 36 && nbPDep[nbPPar[k]!]! < nbPDep[k]! && nbPLab[k]! < 6 &&
          sendsB genP[nbPLab[k]!]!.1 genP[nbPLab[k]!]!.2 n₀[nbPPar[k]!]! n₀[k]!)))

@[expose] def nbQOK : Bool :=
  allLt 6 (fun l => elemOK genQ[l]!.1 genQ[l]!.2 && sendsB genQ[l]!.1 genQ[l]!.2 2835 2835) &&
    nbQ[0]! == 0 &&
    allLt 2997 (fun y => !adjB nbr 2835 y || occB nbQ y) &&
    allLt 315 (fun m => m == 0 ||
      (nbQPar[m]! < 315 && nbQDep[nbQPar[m]!]! < nbQDep[m]! && nbQLab[m]! < 6 &&
        sendsB genQ[nbQLab[m]!]!.1 genQ[nbQLab[m]!]!.2 nbQ[nbQPar[m]!]! nbQ[m]!))

@[expose] def locOK : Bool :=
  adjB nbr 0 p1 && adjB nbr 0 2835 && nbPOK && nbQOK &&
    elemOK swapE.1 swapE.2 && sendsB swapE.1 swapE.2 0 p1 && sendsB swapE.1 swapE.2 p1 0 &&
    cellReps.size == 4 &&
    allLt 4 fun k =>
      let v₁ := actV (cellC' k).1 (cellC' k).2 2835
      pElemOK (cellC k) 2835 cellReps[k]! && pElemOK (cellC' k) 2835 v₁ &&
        sendsB swapE.1 swapE.2 v₁ cellReps[k]!

@[expose] def triOK : Bool :=
  let n₀ := nbr[0]!
  allLt 4 (fun k => triY1[k]! == p1 && triY2[k]! == cellReps[k]!) &&
    allLt 180 (fun t => decide (t < 4) ||
      (triPar[t]! < t && triLab[t]! < 6 &&
        sendsB genP[triLab[t]!]!.1 genP[triLab[t]!]!.2 triY1[triPar[t]!]! triY1[t]! &&
        sendsB genP[triLab[t]!]!.1 genP[triLab[t]!]!.2 triY2[triPar[t]!]! triY2[t]!)) &&
    allLt 18 fun a => allLt 18 fun b =>
      !adjB nbr n₀[a]! n₀[18 + b]! ||
        (triIdx[18 * a + b]! < 180 && triY1[triIdx[18 * a + b]!]! == n₀[a]! &&
          triY2[triIdx[18 * a + b]!]! == n₀[18 + b]!)

@[expose] def classOK : Bool :=
  let s := CFSG.Sporadic.SuzRecog.ModelGroupsData.s1Arr
  CFSG.Sporadic.SuzRecog.Q3A.Check.q3aOK && isInvA 1782 s (invCand 1782 s) &&
    CFSG.Sporadic.SuzOddCore.inM s && conjEq s (invCand 1782 s) rhoArr (compA 1782 rhoArr rhoArr)

@[expose] def groupOK : Bool :=
  let qE := CFSG.ComponentClassification.AS81.SuzB0.qElts
  eqA 1782 (compA 1782 w0Arr (rhoConj w0Arr)) (rhoConj (rhoConj w0Arr)) &&
    allLt 2997 (fun y => !adjB nbr 0 y ||
      (if y < 2835 then y != 0 && (List.range 128).any fun j => eqA 1782 aPts[y]! qE[j]!
       else commA t1Arr wPts[y - 2835]!)) &&
    allLt 128 (fun j =>
      let i := aIdx.getD (fp qE[j]!) 2835
      !(i < 2835 && i != 0 && eqA 1782 aPts[i]! qE[j]!) || adjB nbr 0 i) &&
    allLt 162 (fun j => !commA t1Arr wPts[j]! || adjB nbr 0 (2835 + j)) &&
    commA aPts[p1]! t1Arr && bIdx < 2835 && eqA 1782 aPts[bIdx]! bArr &&
    adjB nbr bIdx cellReps[0]!

end CFSG.Sporadic.SuzRecog.LevelTwo
