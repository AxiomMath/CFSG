
module

public import CFSG.Sporadic.Co2Schreier.WitCheck
public import CFSG.Sporadic.Co2Schreier.CoreCheckBase
public import CFSG.Sporadic.Co2Cert.FaithfulCheck
public import CFSG.Sporadic.Co2Schreier.SylowCheckBase
public meta import CFSG.Sporadic.Co2Schreier.WitCheck
public meta import CFSG.Sporadic.Co2Schreier.SylowCheckBase
public meta import CFSG.Sporadic.Co2Schreier.CoreCheckBase
public meta import CFSG.Sporadic.Co2Cert.FaithfulCheck

public section

namespace CFSG.Sporadic.Co2Schreier

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Monster.B.Mathieu
  CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2.Native

@[expose] def uArr : Array ℕ := compA 2300 sArrs[8]! sArrs[0]!

@[expose] def thirdSteps (S : Array (Array ℕ)) (base : Array ℕ) (j : ℕ) : Array (Array ℕ) :=
  S.foldl (fun acc g => if fixesFirst base g j then (acc.push g).push (invCand 2300 g) else acc)
    #[]

structure TLev where
  pts : Array ℕ
  tr : Array (Array ℕ)
  deriving Inhabited

@[expose] def orbitTr (steps : Array (Array ℕ)) (b : ℕ) : TLev := Id.run do
  let mut pts : Array ℕ := #[b]
  let mut tr : Array (Array ℕ) := #[idA 2300]
  let mut seen : Array Bool := (Array.replicate 2300 false).set! b true
  for h in [0:2300] do
    if h < pts.size then
      let x := pts[h]!
      let tx := tr[h]!
      for g in steps do
        let y := g[x]!
        if !seen[y]! then
          seen := seen.set! y true
          pts := pts.push y
          tr := tr.push (compA 2300 g tx)
  return ⟨pts, tr⟩

@[expose] def thirdLevels (W : WitCert) : Array TLev :=
  let S := extendArrs aArrs W.third.strongDerivations
  let base := W.third.baseIndices.toArray
  (Array.range base.size).map fun j => orbitTr (thirdSteps S base j) base[j]!

@[expose] def dfsCnt (L : Array TLev) (base u : Array ℕ) (ntest : ℕ) :
    ℕ → ℕ → Array ℕ → ℕ
  | 0, _, _ => 1
  | fuel + 1, j, p =>
    if fuel = 0 ∧ ntest ≤ j then L[j]!.tr.size
    else if L[j]!.tr.size = 1 then
      (if j < ntest ∧ u[p[base[j]!]!]! ≠ p[base[j]!]! then 0
        else dfsCnt L base u ntest fuel (j + 1) p)
    else
      (List.range L[j]!.tr.size).foldl (fun acc k =>
        if j < ntest ∧ u[p[(L[j]!.tr[k]!)[base[j]!]!]!]! ≠ p[(L[j]!.tr[k]!)[base[j]!]!]! then acc
        else acc + dfsCnt L base u ntest fuel (j + 1) (compA 2300 p L[j]!.tr[k]!)) 0

@[noinline, expose] def thirdCheck (L : Array TLev) (base u : Array ℕ) (lvP : Array Level)
    (bP : Array ℕ) : Bool :=
  base.size == 13 && allLt 13 (fun j => decide (base[j]! < 2300)) && L.size == 13 &&
    (L.toList.map fun T => T.tr.size) == [2300, 891, 896, 96, 30, 1, 4, 1, 1, 1, 1, 1, 2] &&
    allLt 13 (fun j => eqA 2300 L[j]!.tr[0]! (idA 2300) &&
      allLt L[j]!.tr.size (fun k => isInvA 2300 L[j]!.tr[k]! (invCand 2300 L[j]!.tr[k]!) &&
        fixesFirst base L[j]!.tr[k]! j && siftA 2300 lvP bP 0 L[j]!.tr[k]! &&
        allLt k (fun k' => (L[j]!.tr[k]!)[base[j]!]! != (L[j]!.tr[k']!)[base[j]!]!))) &&
    isInvA 2300 u (invCand 2300 u) && fixesFirst base u 12 &&
    dfsCnt L base u 12 13 0 (idA 2300) == 1474560

@[expose] def matPerm (pt : Array UInt32) (rows : List ℕ) : Array ℕ :=
  let rt := transposeRows 22 rows.toArray
  Array.ofFn (n := 2300) fun i => (pt[vecMulN 22 rt co2PackedVecs[i.val]!]!).toNat

@[expose] def oddMats (W : WitCert) : List (List ℕ) :=
  W.third.odd.sylowThreeGenerators ++ [W.third.odd.sylowFiveGenerator] ++
    W.third.odd.obstructions.map (·.conjugator)

@[expose] def gArrsOf (pt : Array UInt32) (W : WitCert) : Array (Array ℕ) :=
  ((oddMats W).map (matPerm pt)).toArray

@[expose] def eDerivs : List (List ℤ) :=
  [[-6, 7], [-16, -16, -16, -16], [-3, 8], [-18, -18], [19, -17, -19, -19], [-16, -16, -19, 16],
    [-17, -19, 21, 21], [-20, -22], [-23, -20, -21, -20, -16, -16, -22, 16],
    [-20, -23, -21, -23, -16, -23, 16, 18],
    [-24, -25, -20, -23, 21, 20, -16, -19, -19, -10, -3]]

@[expose] def eRecOf (gA : Array (Array ℕ)) (W : WitCert) : ChainRecord where
  degree := 2300
  generators := gA.toList.map Array.toList
  base := W.third.baseIndices
  strongGenerators := (extendArrs gA eDerivs).toList.map Array.toList
  derivations := eDerivs

@[expose] def powA (t : Array ℕ) : ℕ → Array ℕ
  | 0 => idA 2300
  | e + 1 => compA 2300 (powA t e) t

@[expose] def quRecipe : List (List ℕ × ℕ) :=
  [([3], 4), ([5], 6), ([6], 2), ([9], 2), ([10], 6), ([12], 2), ([14], 4), ([0, 2], 3),
    ([0, 4], 4), ([0, 7], 8)]

@[expose] def quArrsOf (gA : Array (Array ℕ)) : Array (Array ℕ) :=
  (quRecipe.map fun r => powA (prodArr gA r.1) r.2).toArray

@[expose] def conjPis (conj : Array (Array ℕ)) (m : ℕ) (E : LeftEnum) : Array (Array ℕ) :=
  conj.map fun c => Array.ofFn (n := m) fun k =>
    E.pos.getD (keyA (compA 2300 (compA 2300 c E.elems[k.val]!) (invCand 2300 c))) 0

@[expose] def wordArrN (n : ℕ) (A : Array (Array ℕ)) (w : List ℤ) : Array ℕ :=
  wordA n A (rawInvs n A) w

@[expose] def extendArrsN (n : ℕ) (A : Array (Array ℕ)) (ds : List (List ℤ)) :
    Array (Array ℕ) :=
  ds.foldl (fun acc w => acc.push (wordArrN n acc w)) A

@[expose] def quDerivs : List (List ℤ) := [[-3, 12], [-7, -16]]

@[expose] def quRecOf (pis : Array (Array ℕ)) : ChainRecord where
  degree := 1024
  generators := pis.toList.map Array.toList
  base := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
  strongGenerators := (extendArrsN 1024 pis quDerivs).toList.map Array.toList
  derivations := quDerivs

@[noinline, expose] def eCheck (pt : Array UInt32) (W : WitCert) (lvP : Array Level)
    (bP : Array ℕ) (u : Array ℕ) : Bool :=
  let gA := gArrsOf pt W
  let eR := eRecOf gA W
  let qA := quArrsOf gA
  let E := leftEnum qA 1024
  let pis := conjPis gA 1024 E
  let qR := quRecOf pis
  (oddMats W).length == 15 && gA.size == 15 && (oddMats W).all rows22OK &&
    allLt 15 (fun i => isInvA 2300 gA[i]! (invCand 2300 gA[i]!) &&
      allLt 2300 (fun k => co2PackedVecs[(gA[i]!)[k]!]! ==
        vecMulN 22 (transposeRows 22 ((oddMats W).getD i []).toArray) co2PackedVecs[k]!) &&
      siftA 2300 lvP bP 0 gA[i]! &&
      eqA 2300 (compA 2300 gA[i]! u) (compA 2300 u gA[i]!)) &&
    chainShapeOK eR 2300 15 26 W.third.baseIndices && recordOK 2300 eR 4 &&
    recordOrbits 2300 eR == [20, 18, 32, 8, 4, 1, 2, 1, 1, 1, 1, 1, 2] &&
    allLt 10 (fun i => isInvA 2300 qA[i]! (invCand 2300 qA[i]!) &&
      eqA 2300 (compA 2300 qA[i]! qA[i]!) (idA 2300) &&
      allLt 10 (fun j => eqA 2300 (compA 2300 qA[i]! qA[j]!) (compA 2300 qA[j]! qA[i]!))) &&
    enumOK qA 1024 E && conjOK gA pis 1024 E &&
    chainShapeOK qR 1024 15 17 [1, 2, 3, 4, 5, 6, 7, 8, 9, 10] && recordOK 1024 qR 4 &&
    recordOrbits 1024 qR == [45, 16, 1, 2, 1, 1, 1, 1, 1, 1]

end CFSG.Sporadic.Co2Schreier
