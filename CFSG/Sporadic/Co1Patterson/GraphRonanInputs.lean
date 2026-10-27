module

public import CFSG.Sporadic.Co1Patterson.GraphRonanDataInputs

public section

namespace CFSG.Sporadic.Co1Patterson.Native

open CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.Co1.InvNative CFSG.Sporadic.Co1Block

@[expose] def d2Reps : List Nat := [0, 2, 3, 4, 6, 7, 9]

@[expose] def farReps : List Nat := [5, 8]

@[expose] def repP (j : Nat) : Rows × Rows := (repX j, repXi j)

@[expose] def adjK (o : Orb) (S : Std.HashSet (Array Nat)) (B : Rows) (k : Nat) : Bool :=
  adjC S (xeK o k) (xeiK o k) B

@[expose] def lvl2Check (o : Orb) (S : Std.HashSet (Array Nat)) (t : Nat) : Bool :=
  let B := repRows (d2Reps.getD t 0)
  let d := lvl2Data.getD t ([], [])
  B != iotaARows && !(S.contains B) && treeIn o S d.1 d.2 (adjK o S B) (adjK o S B)

@[expose] def farCheck (o : Orb) (S : Std.HashSet (Array Nat)) (t : Nat) : Bool :=
  let B := repRows (farReps.getD t 0)
  let pth := farPath.getD t (0, 0)
  let z := nbrX o (xeK o pth.1, xeiK o pth.1) pth.2
  B != iotaARows && !(S.contains B) &&
    (List.range o.c.pts.size).all (fun k => !(adjK o S B k)) &&
    decide (pth.1 < o.c.pts.size) && decide (pth.2 < o.c.pts.size) && adjC S z.1 z.2 B

@[expose] def aeCheck : Bool :=
  decide (1 ≤ aeIdx) && decide (aeIdx ≤ 190) &&
    conjA (gEl aeIdx) (gElInv aeIdx) == mul iotaARows (repRows 1) &&
    !(qPts.contains (mul (mul (repXi 1) iotaARows) (repX 1)))

@[expose] def ronanCheck1 : Bool :=
  let o := orbE
  let S := ptSet o
  aeCheck && (List.range 7).all (lvl2Check o S) && (List.range 2).all (farCheck o S)

@[expose] def lvl3Tree (t : Nat) : List Nat × List Nat :=
  let tx := if t == 0 then lvl3Text0 else lvl3Text1
  (parseNats tx.1, parseNats tx.2)

@[expose] def lvl3Wit (t : Nat) : Std.HashMap Nat Nat :=
  Std.HashMap.ofList (parsePairs (if t == 0 then lvl3WitText0 else lvl3WitText1))

@[expose] def ronanCheck2 (t : Nat) : Bool :=
  let o := orbE
  let S := ptSet o
  let j := farReps.getD t 0
  let B := repRows j
  let tr := lvl3Tree t
  let wit := lvl3Wit t
  treeIn o S tr.1 tr.2 (fun k => dcls S (atK o k B) == 2) (fun k => dcls S (atK o k B) != 3) &&
    (List.range o.c.pts.size).all fun m =>
      let gp := nbrX o (repP j) m
      let G := vtxR gp.1 gp.2
      let d := dcls S G
      d == 1 || d == 2 || (d == 3 &&
        match wit[m]? with
        | some k => decide (k < o.c.pts.size) && dcls S (atK o k B) == 2 &&
            dcls S (atK o k G) == 2
        | none => false)

@[expose] def q2Forest (o : Orb) (t : Nat) : List Orb :=
  let gens := gensKb.getD t []
  ((q2Roots.getD t []).zip (q2Masks.getD t [])).map fun p =>
    let gp := nbrX o (repP (d2Reps.getD t 0)) p.1
    mkOrbT (gensArr gens) (gensInvArr gens) (vtxR gp.1 gp.2) (treeOfMasks 16 64 p.2)

@[expose] def q2Check (t : Nat) : Bool :=
  let o := orbE
  let S := ptSet o
  let j := d2Reps.getD t 0
  let B := repRows j
  let gens := gensKb.getD t []
  let G := gensArr gens
  let Gi := gensInvArr gens
  let roots := q2Roots.getD t []
  let certs := q2Certs.getD t []
  let forest := q2Forest o t
  let fset : Std.HashSet (Array Nat) := Std.HashSet.ofList (forest.flatMap fun f => f.c.pts.toList)
  centOK G B && roots.length == certs.length && forest.length == roots.length &&
    (List.range roots.length).all (fun i =>
      let m := roots.getD i 0
      let gp := nbrX o (repP j) m
      decide (m < o.c.pts.size) && orbOK G Gi (vtxR gp.1 gp.2) (forest.getD i default) &&
        qcOK o S (repP j) gp (certs.getD i default)) &&
    (List.range o.c.pts.size).all fun m =>
      let gp := nbrX o (repP j) m
      let Gm := vtxR gp.1 gp.2
      let d := dcls S Gm
      d == 1 || d == 3 || fset.contains Gm

@[expose] def locOrbs (o : Orb) : List Orb :=
  (triRoots.zip [loc202Masks, loc2348Masks, loc3940Masks]).map fun p =>
    mkOrbT (gensArr gensKe) (gensInvArr gensKe) o.c.pts[p.1]! (treeT p.2)

@[expose] def t192Orb (o : Orb) : Orb :=
  mkOrbT (gensArr gensKe) (gensInvArr gensKe) o.c.pts[t192Root]! (treeT t192Masks)

@[expose] def wP (i : Nat) : Rows × Rows :=
  (mul orbQ.hs[i]! (repX 0), mul (repXi 0) orbQ.his[i]!)

@[expose] def locTriOK (o : Orb) (j : Nat) : Bool :=
  let U := o.c.pts[triRoots.getD j 0]!
  let E := repRows 1
  let A := iotaARows
  let t := gEl (tauIdx.getD j 0)
  let ti := gElInv (tauIdx.getD j 0)
  let r := gEl (rhoIdx.getD j 0)
  let ri := gElInv (rhoIdx.getD j 0)
  let wp := wP (triW.getD j 0)
  let W := vtxR wp.1 wp.2
  let inQw := fun Y => qPts.contains (mul (mul wp.2 Y) wp.1)
  decide (triRoots.getD j 0 < o.c.pts.size) && decide (triW.getD j 0 < orbQ.c.pts.size) &&
    decide (1 ≤ tauIdx.getD j 0) && decide (tauIdx.getD j 0 ≤ 190) &&
    decide (1 ≤ rhoIdx.getD j 0) && decide (rhoIdx.getD j 0 ≤ 190) &&
    mul (mul t A) ti == E && mul (mul t E) ti == A && mul (mul t U) ti == U &&
    mul t W == mul W t && mul (mul r A) ri == E && mul (mul r E) ri == U &&
    mul (mul r U) ri == A && mul r W == mul W r && inQw A && inQw E && inQw U

@[expose] def triCheck : Bool :=
  let o := orbE
  let S := ptSet o
  let E := repRows 1
  let A := iotaARows
  let G := gensArr gensKe
  let Gi := gensInvArr gensKe
  let lo := locOrbs o
  let lset : Std.HashSet (Array Nat) := Std.HashSet.ofList (lo.flatMap fun f => f.c.pts.toList)
  let t1 := t192Orb o
  let tset := ptSet t1
  let s := gEl swapIdx
  let si := gElInv swapIdx
  let U := o.c.pts[t192Root]!
  let Vc := o.c.pts[coneIdx]!
  decide (1 ≤ swapIdx) && decide (swapIdx ≤ 190) &&
    mul (mul s A) si == E && mul (mul s E) si == A && centOK G E &&
    lo.length == triRoots.length &&
    (List.range triRoots.length).all (fun j =>
      orbOK G Gi o.c.pts[triRoots.getD j 0]! (lo.getD j default)) &&
    orbOK G Gi U t1 &&
    (List.range o.c.pts.size).all (fun k =>
      !(adjC S (repX 1) (repXi 1) o.c.pts[k]!) || lset.contains o.c.pts[k]! ||
        tset.contains o.c.pts[k]!) &&
    decide (t192Root < o.c.pts.size) && decide (coneIdx < o.c.pts.size) &&
    decide (coneK2 < o.c.pts.size) &&
    adjC S (repX 1) (repXi 1) Vc && adjC S (xeK o t192Root) (xeiK o t192Root) Vc &&
    lset.contains Vc && lset.contains (mul (mul o.his[t192Root]! Vc) o.hs[t192Root]!) &&
    mul (mul si U) s == o.c.pts[coneK2]! &&
    lset.contains (mul (mul (mul o.his[coneK2]! si) Vc) (mul s o.hs[coneK2]!)) &&
    (List.range triRoots.length).all (locTriOK o)

end CFSG.Sporadic.Co1Patterson.Native
