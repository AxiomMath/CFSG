module

public import CFSG.Sporadic.Co2Smith.GlWInputs
public import CFSG.Sporadic.Co2Smith.GlNJData

public section

namespace CFSG.Sporadic.Co2Smith.Native

open CFSG.Sporadic.SmallF2.Native CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
  CFSG.Sporadic.Co2Cert

set_option compiler.extract_closed false

@[expose] def glNJG (k : Nat) : Array Nat := glR glNJGw[k]!

@[expose] def glNJGt (k : Nat) : Array Nat := mulRows 22 (glJcR glNJTw[k]!) (glNJG k)

@[expose] def glNJGs (s k : Nat) : Array Nat :=
  if k = 1 then mulRows 22 (glJcR s) (glNJG 1) else glNJG k

@[expose] def glNJWord (g : Nat → Array Nat) (w : List Nat) : Array Nat :=
  w.foldr (fun k acc => mulRows 22 (g k) acc) (idRows 22)

@[expose] def glNJFixR (R : Array Nat) : Nat :=
  let T := transposeRows 22 R
  ((List.range 2300).filter fun i => colActT T co2PackedVecs[i]! == co2PackedVecs[i]!).length

@[expose] def glNJPermR (R : Array Nat) : Array Nat :=
  let T := transposeRows 22 R
  Array.ofFn (n := 2300) fun i => (co2PosTable[colActT T co2PackedVecs[i.val]!]!).toNat

@[expose] def glNJT (k x : Nat) : Nat :=
  (List.range 10).foldr (fun i acc => if x.testBit i then (glNJTab[k]!)[i]! ^^^ acc else acc) 0

@[expose] def glNJWordP (w : List Nat) : Array Nat :=
  w.foldr (fun k acc => compA 77 glNJPerm[k]! acc) (idA 77)

@[expose] def glNJJT : Array (Array Nat) :=
  Array.ofFn (n := 1024) fun m => transposeRows 22 (glJcR m.val)

@[expose] def glNJGenOK : Bool :=
  glNJGw.size == 3 && glNJGw.all (fun w => w.all (· < 22)) && glNJTab.size == 3 &&
    glNJTw.length == 3 && glNJTw.all (· < 1024) &&
    commRows (glNJG 0) glZ && commRows (glNJG 1) glZ &&
    (List.range 3).all fun k => glWTabOK (glNJG k) glNJTab[k]! && glWTabOK (glNJGt k) glNJTab[k]!

@[expose] def glNJInjOK : Bool :=
  (List.range 1024).all fun m => m == 0 || glJcR m != idRows 22

@[expose] def glNJOmOK : Bool :=
  glNJOm.length == 77 && glNJOm.all (fun m => decide (0 < m) && decide (m < 1024)) &&
    glNJOm[0]! == 1 &&
    ((List.range 77).all fun i => (List.range 77).all fun j =>
      i == j || glNJOm[i]! != glNJOm[j]!) &&
    glNJPerm.size == 3 &&
    ((List.range 3).all fun i => (glNJPerm[i]!).size == 77 && (List.range 77).all fun k =>
      decide ((glNJPerm[i]!)[k]! < 77) && glNJT i glNJOm[k]! == glNJOm[(glNJPerm[i]!)[k]!]!) &&
    glNJConj.size == 77 &&
    ((List.range 77).all fun k => glNJConj[k]!.all (· < 3) && (glNJWordP glNJConj[k]!)[0]! == k) &&
    glNJSpan.size == 10 &&
    (List.range 10).all fun i => glNJSpan[i]!.all (· < 77) &&
      glNJSpan[i]!.foldl (fun acc k => acc ^^^ glNJOm[k]!) 0 == 2 ^ i

@[expose] def glNJ1OK : Bool := glNJGenOK && glNJInjOK && glNJOmOK

@[expose] def glNJFixOK : Bool :=
  (List.range 1024).all fun m => m == 0 || glNJOm.contains m || glNJFixR (glJcR m) != 284

@[expose] def glNJPtOK (JT : Array (Array Nat)) : Bool :=
  let vp := co2PackedVecs[1]!
  (List.range 3).all (fun k => glMaps (glNJG k) 1 1) &&
    (List.range 1024).all (fun m => m == 0 || colActT JT[m]! vp != vp) &&
    glNJPtJ.size == 2300 &&
    (List.range 2300).all (fun x => decide (glNJPtJ[x]! < 1024) &&
      (colActT JT[glNJPtJ[x]!]! vp == co2PackedVecs[x]! ||
        (glNJPtJ[x]! != 0 &&
          colActT JT[glNJPtJ[x]!]! co2PackedVecs[x]! == co2PackedVecs[x]!))) &&
    glNJBasis.length == 22 &&
    glNJBasis.all (fun x =>
      decide (x < 2300) && colActT JT[glNJPtJ[x]!]! vp == co2PackedVecs[x]!) &&
    glNJBasisInv.size == 22 &&
    mulRows 22 (glNJBasis.toArray.map fun x => co2PackedVecs[x]!) glNJBasisInv == idRows 22

@[expose] def glNJO77OK (JT : Array (Array Nat)) : Bool :=
  glNJO77.all (· < 2300) &&
    ((List.range 3).all fun k =>
      let R := glNJGt k
      let p := glNJPermR R
      glPermOK R p && glNJO77.all fun x => glNJO77.contains p[x]!) &&
    glNJO77Wx.size == 1024 && glNJO77Wy.size == 1024 &&
    (List.range 1024).all fun m => m == 0 ||
      (glNJO77.contains glNJO77Wx[m]! && decide (glNJO77Wy[m]! < 2300) &&
        !glNJO77.contains glNJO77Wy[m]! &&
        colActT JT[m]! co2PackedVecs[glNJO77Wx[m]!]! == co2PackedVecs[glNJO77Wy[m]!]!)

@[expose] def glNJ2OK : Bool :=
  let JT := glNJJT
  glNJPtOK JT && glNJO77OK JT

@[expose] def glNJN (T : Array Bool) (x : Nat) : Nat :=
  (Finset.univ.filter fun k : Fin 77 => T[glNJOm[k.val]! ^^^ x]! = true).card

@[expose] def glNJOmT : Array Bool := Array.ofFn (n := 1024) fun y => glNJOm.contains y.val

@[expose] def glNJNbr : Array (List Nat) :=
  let T := glNJOmT
  Array.ofFn (n := 77) fun a => (List.range 77).filter fun b =>
    b != a.val && glNJN T (glNJOm[a.val]! ^^^ glNJOm[b]!) == 2

@[expose] def glNJColour (nbr : Array (List Nat)) (s : Nat) : Array Nat :=
  refineIter 77 nbr (individualize 77 glNJBase s) 3

@[expose] def glNJClassCount (col : Array Nat) (v : Nat) : Nat :=
  (Finset.univ.filter fun w : Fin 77 => col[w.val]! = col[v]!).card

@[expose] def glNJRefOK : Bool :=
  let nbr := glNJNbr
  nbr.size == 77 && glNJBase.length == 8 && glNJBounds.length == 8 &&
    glNJBase.all (· < 77) &&
    ((List.range 77).all fun a =>
      nbr[a]!.all (· < 77) && CFSG.Certificates.Native.strictIncr nbr[a]!) &&
    ((List.range 8).all fun s =>
      glNJClassCount (glNJColour nbr s) glNJBase[s]! == glNJBounds[s]!) &&
    (glNJColour nbr 8).size == 77 && decide (glNJColour nbr 8).toList.Nodup

@[expose] def glNJ3OK : Bool := glNJRefOK

@[expose] def glNJChainOK : Bool :=
  decide (2 ≤ glNJChS.size) && glNJChS[0]! == glNJPerm[0]! && glNJChS[1]! == glNJPerm[1]! &&
    rawChainOK 77 (glNJChS.extract 0 2) glNJChS glNJChBase.toArray glNJChW 4 &&
    (rawOrbitSizes 77 glNJChS glNJChBase.toArray).prod == 11520

@[expose] def glNJF (c₁ c₂ : Nat) : List Nat → Nat
  | [] => 0
  | k :: w => (if k = 0 then c₁ else c₂) ^^^ glNJT k (glNJF c₁ c₂ w)

@[expose] def glNJH1OK : Bool :=
  let g₀ := glNJG 0
  let g₁ := glNJG 1
  glNJRels.all (fun r => r.all (· < 2) &&
      glNJWord (fun k => if k = 0 then g₀ else g₁) r == idRows 22) &&
    glNJNrm.size == 1024 &&
    ((List.range 1024).all fun x => decide (glNJNrm[x]! < 1024) &&
      [0, 64].contains (x ^^^ glNJNrm[x]! ^^^ glNJT 0 glNJNrm[x]!)) &&
    [0, 64].all fun c₁ => (List.range 1024).all fun c₂ =>
      !(glNJRels.all fun r => glNJF c₁ c₂ r == 0) || (c₁ == 0 && [0, 18, 76, 94].contains c₂)

@[expose] def glNJFusOK : Bool :=
  let x := glNJWord glNJG glNJFusX
  let x' := glNJWord glNJG glNJFusXp
  let a := glNJWord glNJG glNJFusA
  glNJFusA.all (· < 3) && glNJFusX.all (· < 2) && glNJFusXp.all (· < 2) &&
    glNJFusF.length == 4 &&
    mulRows 22 x x == idRows 22 && x != idRows 22 && mulRows 22 a x' == mulRows 22 x a &&
    (List.range 2).all fun i =>
      let s := [18, 94][i]!
      glNJFixR (glNJWord (glNJGs s) glNJFusX) == glNJFusF[2 * i]! &&
        glNJFixR (glNJWord (glNJGs s) glNJFusXp) == glNJFusF[2 * i + 1]! &&
        glNJFusF[2 * i]! != glNJFusF[2 * i + 1]!

@[expose] def glNJ4OK : Bool := glNJH1OK && glNJFusOK

end CFSG.Sporadic.Co2Smith.Native
