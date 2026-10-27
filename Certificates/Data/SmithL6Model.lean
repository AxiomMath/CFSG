module

public import Certificates.Data.SmithEModel
public import Certificates.Data.SmithL6WData

public section

namespace CFSG.SmithL6

open CFSG.SmithE (tri applyCols)

@[expose] def par (x : Nat) : Bool := (List.range 6).foldl (fun b i => b ^^ x.testBit i) false

@[expose] def form (φ x : Nat) : Bool := par (φ &&& x)

@[expose] def det3B (a b c d e f g h i : Bool) : Bool :=
  (a && (e && i ^^ f && h)) ^^ (b && (d && i ^^ f && g)) ^^ (c && (d && h ^^ e && g))

@[expose] def wedge3 (a b c : Nat) : Nat :=
  (List.range 20).foldl (fun acc t =>
    let (r0, r1, r2) := tri[t]!
    if det3B (a.testBit r0) (b.testBit r0) (c.testBit r0) (a.testBit r1) (b.testBit r1)
        (c.testBit r1) (a.testBit r2) (b.testBit r2) (c.testBit r2) then acc ||| 2 ^ t
    else acc) 0

@[expose] def tvList : Array (Nat × Nat) :=
  ((List.range 4096).filterMap fun n =>
    let v := n / 64
    let φ := n % 64
    if v ≠ 0 ∧ φ ≠ 0 ∧ form φ v = false then some (v, φ) else none).toArray

@[expose] def tvPair (k : Nat) : Nat × Nat := tvList[k]!

@[expose] def tvApply (k x : Nat) : Nat :=
  let (v, φ) := tvPair k
  if form φ x then x ^^^ v else x

@[expose] def tvCols (k : Nat) : Array Nat :=
  Array.ofFn (n := 20) fun t =>
    let (a, b, c) := tri[t.val]!
    wedge3 (tvApply k (2 ^ a)) (tvApply k (2 ^ b)) (tvApply k (2 ^ c))

@[expose] def wB (i : Nat) : Nat × Nat × Nat :=
  let c := wData[i]!
  (c % 64, c / 64 % 64, c / 4096)

@[expose] def wt (i : Nat) : Nat := let (a, b, c) := wB i; wedge3 a b c

@[expose] def spanMask (a b c : Nat) : Nat :=
  (List.range 8).foldl (fun acc d =>
    acc ||| 2 ^ ((if d.testBit 0 then a else 0) ^^^ (if d.testBit 1 then b else 0) ^^^
      (if d.testBit 2 then c else 0))) 0

@[expose] def wMask (i : Nat) : Nat := let (a, b, c) := wB i; spanMask a b c

@[expose] def atLeast4 (n : Nat) : Bool :=
  let n1 := n &&& (n - 1)
  let n2 := n1 &&& (n1 - 1)
  let n3 := n2 &&& (n2 - 1)
  n3 != 0

@[expose] def adjW (i j : Nat) : Bool := atLeast4 (wMask i &&& wMask j)

@[expose] def oppW (i j : Nat) : Bool := wMask i &&& wMask j == 1

@[expose] def fB (u v : Nat) : Bool :=
  (List.range 20).foldl (fun b t => b ^^ (u.testBit t && v.testBit (19 - t))) false

end CFSG.SmithL6
