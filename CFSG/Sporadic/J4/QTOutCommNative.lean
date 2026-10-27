module

public import CFSG.Sporadic.J4.QTOutMatNative
public import CFSG.Sporadic.J4.QTOutCommData

public section

namespace CFSG.Sporadic.J4.QT

open CFSG.Sporadic.J4.Native

@[expose] def xorMat (X Y : Array V2) : Array V2 :=
  Array.ofFn (n := 112) fun i => (X[i.val]!).xor (Y[i.val]!)

@[expose] def zeroMat : Array V2 := Array.replicate 112 V2.zero

@[expose] def mat0 : Array V2 := wordRowsOf mWord0

@[expose] def mat1 : Array V2 := wordRowsOf mWord1

@[expose] def mg (g : Nat) : Array V2 := if g = 0 then mat0 else mat1

@[expose] def mgp (g : Nat) : Array V2 := xorMat (mg g) idRows

@[expose] def pathMat (w : List Nat) : Array V2 := w.foldl (fun acc g => mulRows acc (mg g)) idRows

@[expose] def wmat (l : Nat) : Array V2 := pathMat (spinWords.getD l [])

@[expose] def wmats : Array (Array V2) := ((List.range 111).map wmat).toArray

@[expose] def wTabs : Array (Array V2) := wmats.map frTable

@[expose] def bvec (l : Nat) : V2 := frApply (wTabs[l]!) v0Vec

@[expose] def pRows : Array V2 := (((List.range 111).map bvec) ++ [v1Vec]).toArray

@[expose] def pInv : Array V2 := invRows pRows

@[expose] def coordsOf (x : V2) : V2 := frApply (frTable pInv) x

@[expose] def sumW (c : V2) : Array V2 :=
  (List.range 111).foldl (fun acc l => if c.testBit l then xorMat acc (wmats[l]!) else acc) zeroMat

@[expose] def edgeCoords (e : Nat) : V2 :=
  coordsOf (frApply (frTable (mg (kEdges.getD e (0, 0)).2)) (bvec (kEdges.getD e (0, 0)).1))

@[expose] def edgeMat (e : Nat) : Array V2 :=
  xorMat (mulRows (wmats[(kEdges.getD e (0, 0)).1]!) (mg (kEdges.getD e (0, 0)).2))
    (sumW (edgeCoords e))

@[expose] def edgeMats : Array (Array V2) := ((List.range 6).map edgeMat).toArray

@[expose] def mgps : Array (Array V2) := #[mgp 0, mgp 1]

@[expose] def phiOf (mats : Array (Array V2)) (cols : List (Nat × Nat)) : Array V2 :=
  Array.ofFn (n := 112) fun i => V2.ofFn fun m =>
    match cols[m]? with
    | some (e, c) => ((mats[e]!)[i.val]!).testBit c
    | none => false

@[expose] def psiRows (s : Nat) : Array V2 :=
  Array.ofFn (n := 112) fun i => V2.ofFn fun j => decide (s ≤ i.val ∧ j = i.val - s)

@[expose] def v1Coords (g : Nat) : V2 :=
  coordsOf ((frApply (frTable (mg g)) v1Vec).xor v1Vec)

@[expose] def rg (g : Nat) : Array V2 := sumW (v1Coords g)

@[expose] def selV (b : Bool) (x : V2) : V2 := if b then x else V2.zero

@[expose] def kappaComb (b0 b1 b2 b3 : Bool) : V2 :=
  ((selV b0 (bkRows[0]!)).xor (selV b1 (bkRows[1]!))).xor
    ((selV b2 (bkRows[2]!)).xor (selV b3 (bkRows[3]!)))

@[expose] def uComb (b0 b1 b2 b3 : Bool) : V2 :=
  ((selV b0 (u1s[0]!)).xor (selV b1 (u1s[1]!))).xor ((selV b2 (u1s[2]!)).xor (selV b3 (u1s[3]!)))

@[expose] def fixComb (d0 d1 : Bool) : V2 := (selV d0 (bfRows[0]!)).xor (selV d1 (bfRows[1]!))

@[expose] def qRows (u0 u1 : V2) : Array V2 :=
  (((List.range 111).map fun l => frApply (wTabs[l]!) u0) ++ [u1]).toArray

@[expose] def tcomb (b0 b1 b2 b3 d0 d1 : Bool) : Array V2 :=
  mulRows pInv (qRows (kappaComb b0 b1 b2 b3) ((uComb b0 b1 b2 b3).xor (fixComb d0 d1)))

@[expose] def combIdx (b0 b1 b2 b3 d0 d1 : Bool) : Nat :=
  b0.toNat + 2 * b1.toNat + 4 * b2.toNat + 8 * b3.toNat + 16 * d0.toNat + 32 * d1.toNat

@[expose] def jgen (g : Nat) : Array V2 :=
  if g = 0 then rowsA else if g = 1 then rowsB else baseInvs[1]?.getD idRows

@[expose] def jword (w : List Nat) : Array V2 := w.foldl (fun acc g => mulRows acc (jgen g)) idRows

@[expose] def powFuel (M : Array V2) : Nat → Nat → Array V2
  | 0, _ => idRows
  | fuel + 1, e =>
    if e = 0 then idRows
    else
      let r := powFuel (mulRows M M) fuel (e / 2)
      if e % 2 = 1 then mulRows M r else r

@[expose] def powBin (M : Array V2) (e : Nat) : Array V2 := powFuel M 128 e

end CFSG.Sporadic.J4.QT
