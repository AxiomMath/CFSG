module

public import CFSG.Sporadic.Co1Patterson.GraphDataInputs
public import CFSG.Sporadic.Co1Patterson.GraphFixDimInputs
public import CFSG.Sporadic.Co1Block.TwoAQTree
public import CFSG.Sporadic.Co1Patterson.GraphTreeData

public section

namespace CFSG.Sporadic.Co1Patterson.Native

open CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.Co1.InvNative CFSG.Sporadic.Co1.TwoBNative
  CFSG.Sporadic.Co1Block CFSG.Sporadic.SmallF2.Native

@[expose] def brayG : List Rows := Native.brayElts (Native.brayRows iotaARows twoAD1) twoABray

@[expose] def gBase : List Rows :=
  [CFSG.Sporadic.Co1Schreier.Native.aR, CFSG.Sporadic.Co1Schreier.Native.bR, iotaARows] ++
    twoAQRows ++ brayG

@[expose] def gDag : List Rows × List Rows × Bool := dag gBase gWords

@[expose] def gEl (j : Nat) : Rows := gDag.1.getD (j - 1) one

@[expose] def gElInv (j : Nat) : Rows := inv (gEl j)

@[expose] def conjA (x xi : Rows) : Rows := mul (mul x iotaARows) xi

@[expose] def repX (i : Nat) : Rows := gEl (repIdx.getD i 0)

@[expose] def repXi (i : Nat) : Rows := gElInv (repIdx.getD i 0)

@[expose] def repRows (i : Nat) : Rows := conjA (repX i) (repXi i)

@[expose] def dagOK : Bool :=
  gDag.2.2 && gDag.1.length == 190 &&
    (List.range 190).all fun j => validRows (gEl (j + 1)) && validRows (gElInv (j + 1)) &&
      mul (gEl (j + 1)) (gElInv (j + 1)) == one

structure Orb where
  c : ConjCert
  hs : Array Rows
  his : Array Rows
deriving Inhabited

@[expose] def treeHs (G : Array Rows) (c : ConjCert) : Array Rows :=
  (List.range c.pts.size).foldl
    (fun acc i => acc.push (if i == 0 then one else mul G[c.lab[i]!]! acc[c.par[i]!]!)) #[]

@[expose] def treeHis (Gi : Array Rows) (c : ConjCert) : Array Rows :=
  (List.range c.pts.size).foldl
    (fun acc i => acc.push (if i == 0 then one else mul acc[c.par[i]!]! Gi[c.lab[i]!]!)) #[]

@[expose] def mkOrbT (G Gi : Array Rows) (root : Rows) (T : Array Nat × Array Nat) : Orb :=
  let c₀ : ConjCert := ⟨Array.replicate T.1.size root, T.1, T.2⟩
  let hs := treeHs G c₀
  let his := treeHis Gi c₀
  ⟨⟨(Array.range T.1.size).map fun i => mul (mul hs[i]! root) his[i]!, T.1, T.2⟩, hs, his⟩

@[expose] def treeT (ms : List Nat) : Array Nat × Array Nat := treeOfMasks 8 64 ms

@[expose] def orbOK (G Gi : Array Rows) (root : Rows) (o : Orb) : Bool :=
  let n := o.c.pts.size
  decide (0 < n) && o.hs.size == n && o.his.size == n && o.c.par.size == n &&
    o.c.lab.size == n &&
    (List.range G.size).all (fun l => mul G[l]! Gi[l]! == one) &&
    o.hs[0]! == one && o.his[0]! == one &&
    (List.range n).all (fun i => i == 0 || (decide (o.c.par[i]! < i) &&
      decide (o.c.lab[i]! < G.size) && o.hs[i]! == mul G[o.c.lab[i]!]! o.hs[o.c.par[i]!]! &&
      o.his[i]! == mul o.his[o.c.par[i]!]! Gi[o.c.lab[i]!]!)) &&
    (List.range n).all (fun i => validRows o.c.pts[i]! && validRows o.hs[i]! &&
      validRows o.his[i]! && o.c.pts[i]! == mul (mul o.hs[i]! root) o.his[i]!) &&
    distinctKeys (o.c.pts.toList.map rowsKey)

@[expose] def ptSet (o : Orb) : Std.HashSet (Array Nat) := Std.HashSet.ofList o.c.pts.toList

@[expose] def orbClosed (G Gi : Array Rows) (o : Orb) : Bool :=
  let S := ptSet o
  (List.range o.c.pts.size).all fun i =>
    (List.range G.size).all fun l => S.contains (mul (mul G[l]! o.c.pts[i]!) Gi[l]!)

@[expose] def brayArr : Array Rows := brayG.toArray

@[expose] def brayInvArr : Array Rows := brayArr.map inv

@[expose] def orbQ : Orb := mkOrbT brayArr brayInvArr (repRows 0) (treeT orbQMasks)

@[expose] def orbE : Orb := mkOrbT brayArr brayInvArr (repRows 1) (treeT orbEMasks)

@[expose] def orb4c : Orb := mkOrbT brayArr brayInvArr (repRows 3) (treeT orb4cMasks)

@[expose] def exactOK (o : Orb) (root : Rows) (n : Nat) : Bool :=
  orbOK brayArr brayInvArr root o && orbClosed brayArr brayInvArr o && o.c.pts.size == n

@[expose] def gensArr (L : List Nat) : Array Rows := (L.map gEl).toArray

@[expose] def gensInvArr (L : List Nat) : Array Rows := (L.map gElInv).toArray

@[expose] def centOK (G : Array Rows) (z : Rows) : Bool :=
  G.all fun g => mul g iotaARows == mul iotaARows g && mul g z == mul z g

@[expose] def fibreOK (gens : List Nat) (z root : Rows) (n : Nat) (T : Array Nat × Array Nat) :
    Bool :=
  let G := gensArr gens
  let Gi := gensInvArr gens
  let o := mkOrbT G Gi root T
  centOK G z && orbOK G Gi root o && o.c.pts.size == n

@[expose] def conjPt (o : Orb) (x xi : Rows) (i : Nat) (b : Rows) : Rows :=
  mul (mul (mul xi o.his[i]!) b) (mul o.hs[i]! x)

@[expose] def countN (o : Orb) (x xi : Rows) (S : Std.HashSet (Array Nat)) (b : Rows) : Nat :=
  ((List.range o.c.pts.size).filter fun i => S.contains (conjPt o x xi i b)).length

@[expose] def conjValid (o : Orb) (x xi : Rows) (b : Rows) : Bool :=
  (List.range o.c.pts.size).all fun i => validRows (conjPt o x xi i b)

@[expose] def qPts : Std.HashSet (Array Nat) := Std.HashSet.ofList twoAQTree.pts.toList

@[expose] def qTreeOK : Bool := gtOK twoAQRows.toArray twoAQTree

@[expose] def invOK (b : Rows) (o : Nat) (inQ inQ2 : Bool) (d : Nat) : Bool :=
  let ab := mul iotaARows b
  validRows b && validRows (mul ab ab) && orderIs ab o && qPts.contains b == inQ &&
    qPts.contains (mul ab ab) == inQ2 && fixDimIs ab d

@[expose] def invTable : List (Nat × Bool × Bool × Nat) :=
  [(1, true, true, 24), (2, true, true, 16), (2, false, true, 16), (2, false, true, 12),
    (4, false, true, 8), (3, false, false, 12), (3, false, false, 8), (4, false, false, 10),
    (4, false, false, 8), (5, false, false, 8), (6, false, false, 8)]

@[expose] def rep11 (i : Nat) : Rows := if i == 0 then iotaARows else repRows (i - 1)

@[expose] def invCheck : Bool :=
  (List.range 11).all fun i =>
    let t := invTable.getD i (0, false, false, 0)
    invOK (rep11 i) t.1 t.2.1 t.2.2.1 t.2.2.2

@[expose] def orbA4 : Orb := mkOrbT brayArr brayInvArr (repRows 2) (treeT orbA4Masks)

@[expose] def eRows : Rows := repRows 1

@[expose] def zRows : Rows := repRows 0

@[expose] def suborbCheck1 : Bool :=
  dagOK && qTreeOK && exactOK orbQ zRows 270 && exactOK orbE eRows 12600

@[expose] def suborbCheck2 : Bool := exactOK orb4c (repRows 3) 34560

@[expose] def suborbCheck3 : Bool :=
  orbOK brayArr brayInvArr (repRows 2) orbA4 && orbA4.c.pts.size == 60480 && invCheck

@[expose] def suborbCheck4 : Bool :=
  let ab4a := mul iotaARows (repRows 6)
  let ab4b := mul iotaARows (repRows 7)
  let ab6 := mul iotaARows (repRows 9)
  mul ab4a ab4a == eRows && mul ab4b ab4b == eRows && mul (mul ab6 ab6) ab6 == eRows &&
    fibreOK gensKe eRows (repRows 6) 384 (treeT fib6Masks) &&
    fibreOK gensKe eRows (repRows 7) 192 (treeT fib7Masks) &&
    fibreOK gensKe eRows (repRows 9) 2048 (treeT fib9Masks)

@[expose] def suborbCheck5 : Bool :=
  let SE := ptSet orbE
  let S4 := ptSet orb4c
  let xe := repX 1
  let xei := repXi 1
  let xq := repX 0
  let xqi := repXi 0
  SE.contains (mul (mul xei (repRows 4)) xe) && S4.contains (mul (mul xei (repRows 8)) xe) &&
    S4.contains (mul (mul xqi (repRows 5)) xq) && conjValid orbE xe xei (repRows 4) &&
    conjValid orbE xe xei (repRows 8) && conjValid orbQ xq xqi (repRows 5) &&
    countN orbE xe xei SE (repRows 4) == 45 && countN orbE xe xei S4 (repRows 8) == 25 &&
    countN orbQ xq xqi S4 (repRows 5) == 9 &&
    fibreOK gensKe eRows (repRows 4) 2048 (treeT fib4Masks) &&
    fibreOK gensKe eRows (repRows 8) 24576 (treeT fib8Masks) &&
    fibreOK gensKz zRows (repRows 5) 16384 (treeT fib5Masks)

end CFSG.Sporadic.Co1Patterson.Native
