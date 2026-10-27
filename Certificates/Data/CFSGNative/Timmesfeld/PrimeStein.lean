module

public import Std.Data.HashSet

public section

set_option compiler.extract_closed false

namespace CFSG.PrimeSteinNative

@[expose] def allLtGo (n : Nat) (f : Nat → Bool) (i : Nat) : Bool :=
  if i < n then (if f i then allLtGo n f (i + 1) else false) else true
termination_by n - i

@[expose] def allLt (n : Nat) (f : Nat → Bool) : Bool := allLtGo n f 0

@[expose] def digitsP (p r n : Nat) : List Nat := (List.range r).map fun j => n / p ^ j % p

@[expose] def ofDigitsP (p : Nat) (l : List Nat) : Nat := l.foldr (fun d acc => d + p * acc) 0

@[expose] def reflAux (p bi : Nat) (b row : List Nat) : List Nat :=
  List.zipWith (fun bj cj => (bj + cj * bi) % p) b row

@[expose] def reflL (p : Nat) (rows : List (List Nat)) (i : Nat) (b : List Nat) : List Nat :=
  reflAux p (b.getD i 0) b (rows.getD i [])

@[expose] def actL (p : Nat) (rows : List (List Nat)) (word : List Nat) (b : List Nat) :
    List Nat :=
  word.foldr (reflL p rows) b

@[expose] def reflIdx (p r : Nat) (rows : List (List Nat)) (i n : Nat) : Nat :=
  ofDigitsP p (reflL p rows i (digitsP p r n))

structure OrbitTab where
  reps : List (List Nat)
  gen : Array Nat
  src : Array Nat
  dep : Array Nat

@[expose] def orbitGen (p r : Nat) (rows : List (List Nat)) : OrbitTab := Id.run do
  let N := p ^ r
  let mut gen : Array Nat := Array.replicate N 0
  let mut src : Array Nat := Array.replicate N 0
  let mut dep : Array Nat := Array.replicate N 0
  let mut seen : Array Bool := Array.replicate N false
  let mut reps : Array (List Nat) := #[]
  for v0 in [0:N] do
    if !(seen[v0]!) then
      let k := reps.size
      reps := reps.push (digitsP p r v0)
      seen := seen.set! v0 true
      gen := gen.set! v0 r
      src := src.set! v0 k
      dep := dep.set! v0 0
      let mut queue : Array Nat := #[v0]
      let mut head := 0
      while head < queue.size do
        let u := queue[head]!
        head := head + 1
        for i in [0:r] do
          let w := reflIdx p r rows i u
          if !(seen[w]!) then
            seen := seen.set! w true
            gen := gen.set! w i
            src := src.set! w u
            dep := dep.set! w (dep[u]! + 1)
            queue := queue.push w
  return { reps := reps.toList, gen := gen, src := src, dep := dep }

@[expose] def orbitOKAt (p r : Nat) (rows : List (List Nat)) (T : OrbitTab) (v : Nat) : Bool :=
  if T.gen.getD v 0 < r then
    decide (T.src.getD v 0 < p ^ r) &&
      decide (T.dep.getD (T.src.getD v 0) 0 < T.dep.getD v 0) &&
      (reflL p rows (T.gen.getD v 0) (digitsP p r (T.src.getD v 0)) == digitsP p r v)
  else
    decide (T.src.getD v 0 < T.reps.length) &&
      (T.reps.getD (T.src.getD v 0) [] == digitsP p r v) && decide (T.dep.getD v 0 = 0)

@[expose] def orbitOK (p r : Nat) (rows : List (List Nat)) (T : OrbitTab) : Bool :=
  decide (T.gen.size = p ^ r) && decide (T.src.size = p ^ r) && decide (T.dep.size = p ^ r) &&
    T.reps.all (fun b => decide (b.length = r)) && allLt (p ^ r) (orbitOKAt p r rows T)

structure RTab where
  vecs : Array (List Int)
  hts : Array Int
  imgs : Array (Array Nat)

@[expose] def dotL (a b : List Int) : Int := (List.zipWith (· * ·) a b).sum

@[expose] def imgL (T : RTab) (i : Nat) (t : List Nat) : List Nat :=
  t.map fun k => (T.imgs.getD i #[]).getD k 0

@[expose] def hsL (T : RTab) (t : List Nat) : List Int := t.map fun k => T.hts.getD k 0

@[expose] def dTestL (Δv : List (List Int)) (hs : List Int) : Bool :=
  Δv.all fun bv => decide (0 < dotL bv hs)

@[expose] def decodeT (r k : Nat) : List Nat := (List.range r).map fun j => k / 256 ^ j % 256

@[expose] def encodeT (t : List Nat) : Nat := t.foldr (fun x acc => x + 256 * acc) 0

@[expose] def chiTestL (p r : Nat) (T : RTab) (vec : List Nat) (t : List Nat) : Bool :=
  (List.range r).all fun j =>
    decide ((dotL (T.vecs.getD (t.getD j 0) []) (vec.map fun x : Nat => (x : Int)) -
      ((vec.getD j 0 : Nat) : Int)) % (p : Int) = 0)

structure StabData where
  simple : List Nat
  keys : List Nat

@[expose] def posKerRoots (p nroots : Nat) (T : RTab) (vec : List Nat) : List Nat :=
  (List.range nroots).filter fun β =>
    decide (0 < T.hts.getD β 0) &&
      decide ((dotL (T.vecs.getD β []) (vec.map fun x : Nat => (x : Int))) % (p : Int) = 0)

@[expose] def simpleKerRoots (p nroots : Nat) (T : RTab) (vec : List Nat) : List Nat :=
  let pk := posKerRoots p nroots T vec
  let vs := pk.map fun β => T.vecs.getD β []
  pk.filter fun β =>
    !(vs.any fun γ => vs.any fun δ => List.zipWith (· + ·) γ δ == T.vecs.getD β [])

@[expose] def stabGen (p r nroots : Nat) (T : RTab) (vec : List Nat) : StabData := Id.run do
  let simple := simpleKerRoots p nroots T vec
  let Δv := simple.map fun β => T.vecs.getD β []
  let idt := List.range r
  let mut set : Std.HashSet Nat := (∅ : Std.HashSet Nat).insert (encodeT idt)
  let mut queue : Array (List Nat) := #[idt]
  let mut head := 0
  while head < queue.size do
    let t := queue[head]!
    head := head + 1
    for i in [0:r] do
      let img := imgL T i t
      if dTestL Δv (hsL T img) then
        let c := encodeT img
        if !(set.contains c) then
          set := set.insert c
          queue := queue.push img
  return { simple := simple, keys := queue.toList.map encodeT }

@[expose] def stepAuxP (r : Nat) (T : RTab) (Δv : List (List Int)) (set : Std.HashSet Nat)
    (img : List Nat) : Bool :=
  !(dTestL Δv (hsL T img)) ||
    (decide (decodeT r (encodeT img) = img) && set.contains (encodeT img))

@[expose] def stabCheck (p r nroots : Nat) (T : RTab) (vec : List Nat) (S : StabData) : Bool :=
  let set : Std.HashSet Nat := Std.HashSet.ofList S.keys
  let Δv : List (List Int) := S.simple.map fun β => T.vecs.getD β []
  set.contains (encodeT (List.range r)) &&
    decide (decodeT r (encodeT (List.range r)) = List.range r) &&
    S.simple.all (fun β => decide (β < nroots) && decide (0 < T.hts.getD β 0) &&
      decide ((dotL (T.vecs.getD β []) (vec.map fun x : Nat => (x : Int))) % (p : Int) = 0)) &&
    S.keys.all fun k => (List.range r).all fun i =>
      stepAuxP r T Δv set (imgL T i (decodeT r k))

@[expose] def passingCount (p r : Nat) (T : RTab) (vec : List Nat) (S : StabData) : Nat :=
  (S.keys.filter fun k => chiTestL p r T vec (decodeT r k)).length

@[expose] def repCheck (p r nroots : Nat) (T : RTab) (vec : List Nat) : Bool :=
  let S := stabGen p r nroots T vec
  stabCheck p r nroots T vec S && decide (passingCount p r T vec S ≤ 1)

@[expose] def fullCheck (p r nroots : Nat) (rows : List (List Nat)) (T : RTab) : Bool :=
  let O := orbitGen p r rows
  orbitOK p r rows O && O.reps.all fun b => repCheck p r nroots T b

end CFSG.PrimeSteinNative
