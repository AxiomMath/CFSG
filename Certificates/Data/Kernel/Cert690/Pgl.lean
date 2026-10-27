module

public import Certificates.Data.Kernel.Cert690.CBase

public section

namespace CFSG.KC.C690

open CFSG.GF2Type.Smith1979W3.Cert690 CFSG.LargeExtraspecial.O62

@[expose] noncomputable def invsL (E : List Nat) : List Nat := E.map fun x => invGo x E.length x

@[expose] noncomputable def isInvF (x : Nat) : Bool := x != oneF && mulF x x == oneF

@[expose] noncomputable def lookD (E V : List Nat) (c d : Nat) : Nat := ((E.zip V).lookup c).getD d

@[expose] noncomputable def involL (E : List Nat) : List Nat := E.filter isInvF

@[expose] noncomputable def outersL (K K0 : List Nat) : List Nat :=
  (involL K).filter fun u => !(K0.contains u)

@[expose] noncomputable def findCommK (K invK : List Nat) (t : Nat) : Option (Nat × Nat) :=
  (List.range K.length).findSome? fun i =>
    (List.range K.length).findSome? fun j =>
      if mulF (mulF (mulF K[i]! K[j]!) invK[i]!) invK[j]! == t then some (i, j) else none

@[expose] noncomputable def commWitL (K : List Nat) : List (Option (Nat × Nat)) :=
  kPGL0Gens.map fun t => findCommK K (invsL K) t

@[expose] def f5WitK : Array (Nat × Nat) :=
  Array.ofFn (n := 64) fun n =>
    ((List.range vPlusVecs.length).findSome? fun i =>
      (List.range vStarVecs.length).findSome? fun j =>
        if vPlusVecs[i]! ^^^ vStarVecs[j]! == n.val then
          some (vPlusVecs[i]!, vStarVecs[j]!)
        else none).getD (0, 0)

@[expose] noncomputable def w9K (K : List Nat) : Array Nat :=
  Array.ofFn (n := 64) fun v =>
    if v.val == 0 then 0
    else ((List.range K.length).find? fun i => actF K[i]! 2 == v.val).getD K.length

@[expose] noncomputable def w12L (K K0 : List Nat) : List Nat :=
  (outersL K K0).map fun u' =>
    ((List.range K.length).find? fun i =>
      mulF (mulF K[i]! (outersL K K0)[0]!) (invsL K)[i]! == u').getD K.length

@[expose] noncomputable def mulIdxTableK (A : Array Nat) : Array (Array Nat) :=
  Array.ofFn (n := A.size) fun i =>
    Array.ofFn (n := A.size) fun j => A.toList.idxOf (mulF (A[i.val]!) (A[j.val]!))

@[expose] noncomputable def conjIdxTableK (A K invK : Array Nat) : Array (Array Nat) :=
  Array.ofFn (n := K.size) fun h =>
    Array.ofFn (n := A.size) fun i =>
      A.toList.idxOf (mulF (mulF (K[h.val]!) (A[i.val]!)) (invK[h.val]!))

@[expose] noncomputable def centralMaskTableK (A K : Array Nat) : Array Nat :=
  Array.ofFn (n := K.size) fun h =>
    (List.range A.size).foldl
      (fun m i =>
        if mulF (K[h.val]!) (A[i]!) == mulF (A[i]!) (K[h.val]!) then
          m ||| (1 <<< i)
        else m)
      0

@[expose] noncomputable def powGoF (a : Nat) : Nat → Nat → Nat
  | 0, acc => acc
  | f + 1, acc => powGoF a f (mulF acc a)

@[expose] noncomputable def pow2F (a : Nat) : Bool := powGoF a 16 oneF == oneF

@[expose] noncomputable def pglF1K (elems invs elems0 invs0 : Array Nat) : Bool :=
  invs.size == elems.size &&
  (List.range elems.size).all (fun i => mulF (elems[i]!) (invs[i]!) == oneF) &&
  invs0.size == elems0.size &&
  (List.range elems0.size).all (fun i => mulF (elems0[i]!) (invs0[i]!) == oneF)

@[expose] noncomputable def pglF4K (elems elems0 invs : Array Nat) (iv : Nat → Nat)
    (commWit : Array (Option (Nat × Nat))) : Bool :=
  elems0.toList.all (fun x => elems.toList.contains x) &&
  (kPGL0Gens.all fun x => kPGLGens.all fun g =>
    mulF g (iv g) == oneF && elems0.toList.contains (mulF (mulF g x) (iv g))) &&
  (kPGLGens.all fun g => kPGLGens.all fun h =>
    mulF g (iv g) == oneF && mulF h (iv h) == oneF &&
    elems0.toList.contains (mulF (mulF (mulF g h) (iv g)) (iv h))) &&
  commWit.size == kPGL0Gens.length &&
  (List.range kPGL0Gens.length).all fun j =>
    match commWit[j]! with
    | some (i, x) =>
      decide (i < elems.size) && decide (x < elems.size) &&
      mulF (mulF (mulF (elems[i]!) (elems[x]!)) (invs[i]!)) (invs[x]!) == kPGL0Gens[j]!
    | none => false

@[expose] def pglF5K (f5Wit : Array (Nat × Nat)) : Bool :=
  vPlusVecs.all (fun v => qB false v == false) &&
  vStarVecs.all (fun v => qB false v == false) &&
  vPlusVecs.filter (fun v => vStarVecs.contains v) == [0] &&
  f5Wit.size == 64 &&
  (List.range 64).all fun n =>
    let p := f5Wit[n]!
    vPlusVecs.contains p.1 && vStarVecs.contains p.2 && (p.1 ^^^ p.2) == n

@[expose] noncomputable def mapsIntoK (g : Nat) (L : List Nat) : Bool :=
  L.all fun v => L.contains (actF g v)

@[expose] noncomputable def mapsIntoListK (g : Nat) (L M : List Nat) : Bool :=
  L.all fun v => M.contains (actF g v)

@[expose] noncomputable def pglF6K : Bool :=
  kPGL0Gens.all fun g => mapsIntoK g vPlusVecs && mapsIntoK g vStarVecs

@[expose] noncomputable def pglF7K (elems elems0 : Array Nat) : Bool :=
  elems.toList.all fun k =>
    if elems0.toList.contains k then true
    else mapsIntoListK k vPlusVecs vStarVecs && mapsIntoListK k vStarVecs vPlusVecs

@[expose] def spanK (S : List Nat) : Array Nat :=
  S.foldl
    (fun (B : Array Nat) e => if B.toList.contains e then B else B ++ (B.toList.map fun x => x ^^^ e).toArray)
    #[0]

@[expose] def sameSetK (B : Array Nat) (L : List Nat) : Bool :=
  B.size == L.length && L.all (fun x => B.toList.contains x) && B.toList.all (fun x => L.contains x)

@[expose] noncomputable def pglF8K (elems0 : Array Nat) : Bool :=
  (List.range 64).all fun n =>
    if n == 0 then true
    else
      let B := spanK (elems0.toList.map fun k => actF k n)
      (B.size == 8 && sameSetK B vPlusVecs) || (B.size == 8 && sameSetK B vStarVecs) ||
        B.size == 64

@[expose] noncomputable def pglF9K (elems w9 : Array Nat) : Bool :=
  let vs := (vPlusVecs ++ vStarVecs).filter fun v => v != 0
  vs.contains 2 && w9.size == 64 &&
  vs.all fun e' =>
    let i := w9[e']!
    decide (i < elems.size) && actF (elems[i]!) 2 == e'

@[expose] noncomputable def pglInvolutionsK (elems involutions : Array Nat) : Bool :=
  elems.toList.all (fun x => isInvF x == involutions.toList.contains x) &&
  involutions.toList.all (fun x => elems.toList.contains x)

@[expose] noncomputable def pglOutersK (elems elems0 outers : Array Nat) : Bool :=
  elems.toList.all (fun x =>
    (isInvF x && !(elems0.toList.contains x)) == outers.toList.contains x) &&
  outers.toList.all (fun x => elems.toList.contains x)

@[expose] def badMaskK (B : Array Bool) (n : Nat) : Nat :=
  (List.range n).foldl (fun acc i => if B[i]! then acc else acc ||| (1 <<< i)) 0

@[expose] def f10Vecs : List Nat :=
  (List.range 64).filter fun e =>
    e != 0 && !(qB false e) && !(vPlusVecs.contains e) && !(vStarVecs.contains e)

@[expose] noncomputable def f10At (elems invs : Array Nat) (e : Nat) : Bool :=
    let C := elems.filter fun k => actF k e == e
    let n := C.size
    let M := mulIdxTableK C
    let isInv := (C.toList.map (fun a => mulF a a == oneF)).toArray
    let oneIdx := C.toList.idxOf oneF
    let conj := conjIdxTableK C elems invs
    let cent := centralMaskTableK C elems
    let badCent := (List.range elems.size).foldl
      (fun acc i => if pow2F (elems[i]!) then acc else acc.push (cent[i]!)) #[]
    if n == 16 then
      let mexact := (List.range n).all fun i =>
        (List.range n).all fun j =>
          let m := (M[i]!)[j]!
          decide (m < n) && C[m]! == mulF (C[i]!) (C[j]!)
      let cexact := (List.range elems.size).all fun h =>
        (List.range n).all fun i =>
          let y := (conj[h]!)[i]!
          let z := mulF (mulF (elems[h]!) (C[i]!)) (invs[h]!)
          (decide (y < n) && C[y]! == z) || (y == n && !(C.toList.contains z))
      C.toList.dedup.length == C.size &&
      decide (oneIdx < n) && C[oneIdx]! == oneF &&
      mexact && cexact &&
      (List.range (2 ^ n)).all fun mask =>
        if (mask &&& badMaskK isInv n == 0) &&
            (mask.testBit oneIdx && decide (4 ≤ bitCount n mask)) then
          if maskClosed M mask n then
            let normEq := (List.range elems.size).all fun h =>
              normalizesMask (conj[h]!) mask n == (actF (elems[h]!) e == e)
            let bad2 := badCent.toList.any fun m => (mask &&& m) == mask
            !normEq || bad2
          else true
        else true
    else false

@[expose] noncomputable def pglF10K (elems invs : Array Nat) : Bool :=
  f10Vecs.all fun e => f10At elems invs e

@[expose] noncomputable def f11At (elems : Array Nat) (u : Nat) : Bool :=
    let C := elems.filter fun k => mulF k u == mulF u k
    let n := C.size
    let M := mulIdxTableK C
    let invC := (invsL C.toList).toArray
    let conjC := conjIdxTableK C C invC
    let oneIdx := C.toList.idxOf oneF
    let uIdx := C.toList.idxOf u
    let pow2 := (C.toList.map (fun a => pow2F a)).toArray
    if n == 12 then
      let mexact := (List.range n).all fun i =>
        (List.range n).all fun j =>
          let m := (M[i]!)[j]!
          decide (m < n) && C[m]! == mulF (C[i]!) (C[j]!)
      let cexact := (List.range n).all fun h =>
        (List.range n).all fun i =>
          let y := (conjC[h]!)[i]!
          let z := mulF (mulF (C[h]!) (C[i]!)) (invC[h]!)
          (decide (y < n) && C[y]! == z) || (y == n && !(C.toList.contains z))
      let invOK := invC.size == n &&
        (List.range n).all (fun i => mulF (C[i]!) (invC[i]!) == oneF)
      C.toList.dedup.length == C.size &&
      decide (oneIdx < n) && C[oneIdx]! == oneF &&
      decide (uIdx < n) && C[uIdx]! == u &&
      invOK && mexact && cexact &&
      (List.range (2 ^ n)).all fun mask =>
        if (mask &&& badMaskK pow2 n == 0) && (mask.testBit oneIdx && maskClosed M mask n &&
            (List.range n).all (fun c => normalizesMask (conjC[c]!) mask n)) then
          (List.range n).all fun i => !(mask.testBit i) || i == oneIdx || i == uIdx
        else true
    else false

@[expose] noncomputable def pglF11K (elems elems0 outers : Array Nat) : Bool :=
  pglOutersK elems elems0 outers && outers.toList.all fun u => f11At elems u

@[expose] noncomputable def pglF12K (elems elems0 invs involutions outers w12 : Array Nat) :
    Bool :=
  pglInvolutionsK elems involutions && pglOutersK elems elems0 outers &&
  outers.size != 0 && w12.size == outers.size &&
  (List.range outers.size).all fun j =>
    let i := w12[j]!
    decide (i < elems.size) &&
    mulF (mulF (elems[i]!) outers[0]!) (invs[i]!) == outers[j]!

@[expose] noncomputable def pglF13K (elems elems0 : Array Nat) : Bool :=
  (elems0.toList.filter fun w => w != oneF && mulF w w == oneF).all fun w =>
    (elems.toList.filter fun k => mulF k w == mulF w k).length == 16 &&
    ((List.range 64).filter fun v => actF w v == v).length == 16

end CFSG.KC.C690

end
