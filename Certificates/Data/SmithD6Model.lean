module

public import Certificates.Data.Kernel.SmithD6.Data

public noncomputable section

namespace CFSG.SmithD6

@[expose] def par6 (x : Nat) : Bool := ((0x6996966996696996 : Nat) >>> x) &&& 1 == 1

@[expose] def qf (x : Nat) : Bool := par6 ((x &&& 63) &&& (x >>> 6))

@[expose] def bf (x y : Nat) : Bool :=
  par6 ((x &&& 63) &&& (y >>> 6)) ^^ par6 ((y &&& 63) &&& (x >>> 6))

@[expose] def sgl (u w x : Nat) : Nat :=
  (x ^^^ (if bf x w then u else 0)) ^^^ (if bf x u then w else 0)

@[expose] def singArr : Array Nat :=
  ((List.range 4096).filter fun x => x != 0 && !qf x).toArray

@[irreducible] def lineKeys : Array Nat := ⟨CFSG.KD.SmithD6.J.lineKeysC.flatten⟩

@[expose] def linePair (k : Nat) : Nat × Nat := (lineKeys[k]! / 4096, lineKeys[k]! % 4096)

@[expose] def lowerBoundGo (A : Array Nat) (k : Nat) : Nat → Nat → Nat → Nat
  | 0, lo, _ => lo
  | fuel + 1, lo, hi =>
    if lo < hi then
      let mid := (lo + hi) / 2
      if A[mid]! < k then lowerBoundGo A k fuel (mid + 1) hi else lowerBoundGo A k fuel lo mid
    else lo

@[expose] def lineIdx (u w : Nat) : Nat :=
  let k := 4096 * u + w
  let i := lowerBoundGo lineKeys k 40 0 lineKeys.size
  if i < 365211 && lineKeys[i]! == k then i else 365211

@[expose] def lineIdx3 (x y z : Nat) : Nat :=
  let lo := min x (min y z)
  let hi := max x (max y z)
  lineIdx lo (lo ^^^ hi)

@[expose] def tvImg (j a : Nat) : Nat :=
  let p := linePair j
  let q := linePair a
  let x1 := sgl p.1 p.2 q.1
  let x2 := sgl p.1 p.2 q.2
  lineIdx3 x1 x2 (x1 ^^^ x2)

@[expose] def evens : Array Nat := ((List.range 64).filter fun s => !par6 s).toArray

@[expose] def evPos : Array Nat :=
  Array.ofFn (n := 64) fun s => ((List.range s.val).filter fun t => !par6 t).length

@[expose] def clg (i S : Nat) : Nat :=
  if i < 6 then (if S.testBit i then 64 else S ||| 2 ^ i)
  else (if S.testBit (i - 6) then S ^^^ 2 ^ (i - 6) else 64)

@[expose] def clg2 (i j c : Nat) : Nat :=
  let S1 := clg j evens[c]!
  if S1 == 64 then 0 else
  let S2 := clg i S1
  if S2 == 64 then 0 else 2 ^ evPos[S2]!

def pairMat : Array Nat :=
  Array.ofFn (n := 144) fun t =>
    (List.range 32).foldl (fun acc c => acc ||| (clg2 (t.val / 12) (t.val % 12) c <<< (32 * c))) 0

@[expose] def applyCols (cols : Array Nat) (c : Nat) : Nat :=
  (List.range cols.size).foldl (fun acc m => if c.testBit m then acc ^^^ cols[m]! else acc) 0

@[expose] def bitsOf (x : Nat) : List Nat := (List.range 12).filter fun i => x.testBit i

@[expose] def tvCols (k : Nat) : Array Nat :=
  let p := linePair k
  let A := (bitsOf p.1).foldl
    (fun acc i => (bitsOf p.2).foldl (fun acc j => acc ^^^ pairMat[i * 12 + j]!) acc) 0
  Array.ofFn (n := 32) fun c => ((A >>> (32 * c.val)) &&& 0xFFFFFFFF) ^^^ 2 ^ c.val

@[expose] def fB (u v : Nat) : Bool :=
  (List.range 32).foldl (fun b t => b ^^ (u.testBit t && v.testBit (31 - t))) false

@[expose] def eV (i : Nat) : Nat := 2 ^ i

@[expose] def fV (i : Nat) : Nat := 2 ^ (6 + i)

@[expose] def lineOf (x y : Nat) : Nat := lineIdx3 x y (x ^^^ y)

def gensArr : Array Nat :=
  #[lineOf (eV 0) (eV 1)] ++
    ((List.range 5).flatMap fun i =>
      [lineOf (eV i) (fV (i + 1)), lineOf (fV i) (eV (i + 1))]).toArray ++
    #[lineOf (eV 4) (eV 5), lineOf (fV 4) (fV 5)]

@[expose] def treeBFS (n : Nat) (gens : Array Nat) (f : Nat → Nat → Nat) (roots : List Nat) :
    Array Nat × Array Nat × Array Nat := Id.run do
  let mut par := Array.replicate n n
  let mut gen := Array.replicate n 0
  let mut dep := Array.replicate n (n + 1)
  let mut queue : Array Nat := #[]
  for r in roots do
    dep := dep.set! r 0
    queue := queue.push r
  let mut head := 0
  for _ in [0:n] do
    if head < queue.size then
      let u := queue[head]!
      head := head + 1
      for g in gens do
        let v := f g u
        if v < n && n < dep[v]! then
          dep := dep.set! v (dep[u]! + 1)
          par := par.set! v u
          gen := gen.set! v g
          queue := queue.push v
  return (par, gen, dep)

@[expose] def treeOK (n m : Nat) (isRoot : Nat → Bool) (edge : Nat → Nat → Nat → Bool)
    (t : Array Nat × Array Nat × Array Nat) : Bool :=
  (List.range n).all fun v => isRoot v || (decide (t.1[v]! < n) && decide (t.2.1[v]! < m) &&
    decide (t.2.2[t.1[v]!]! < t.2.2[v]!) && edge t.2.1[v]! t.1[v]! v)

@[expose] def fBasis : Array Nat := #[64, 128, 256, 512, 1024, 2048]

@[expose] def xorComb (B : Array Nat) (d : Nat) : Nat :=
  (List.range 6).foldl (fun acc m => if d.testBit m then acc ^^^ B[m]! else acc) 0

@[expose] def coefOf (P : Array Nat) (x : Nat) : Nat :=
  (List.range 6).foldl (fun c m => if x.testBit P[m]! then c ||| 2 ^ m else c) 0

@[expose] def memR (B P : Array Nat) (x : Nat) : Bool := xorComb B (coefOf P x) == x

@[expose] def rrefAdd (st : Array Nat × Array Nat) (v : Nat) : Array Nat × Array Nat :=
  let v' := (List.range st.1.size).foldl
    (fun v m => if v.testBit st.2[m]! then v ^^^ st.1[m]! else v) v
  if v' == 0 then st else
    let p := v'.log2
    ((st.1.map fun b => if b.testBit p then b ^^^ v' else b).push v', st.2.push p)

@[expose] def rrefOf (vs : Array Nat) : Array Nat × Array Nat := vs.foldl rrefAdd (#[], #[])

@[expose] def gensCols : Array (Array Nat) := gensArr.map tvCols

@[expose] def gensPair : Array (Nat × Nat) := gensArr.map linePair

@[irreducible] def wtArr : Array Nat := ⟨CFSG.KD.SmithD6.J.wtC.flatten⟩

@[irreducible] def pbArr : Array (Array Nat) := ⟨CFSG.KD.SmithD6.J.pbC.flatten⟩

@[irreducible] def ppArr : Array (Array Nat) := ⟨CFSG.KD.SmithD6.J.ppC.flatten⟩

@[expose] def wtIdx (s : Nat) : Nat :=
  let i := lowerBoundGo wtArr s 40 0 wtArr.size
  if i < 75735 && wtArr[i]! == s then i else 75735

@[expose] def planeImg (k i : Nat) : Nat := wtIdx (applyCols (tvCols k) wtArr[i]!)

@[expose] def planeImgM (G : Array Nat) (i : Nat) : Nat := wtIdx (applyCols G wtArr[i]!)

@[expose] def wt (i : Nat) : Nat := wtArr[i]!

@[expose] def adjW (i j : Nat) : Bool := wt i == wt j || decide (wtIdx (wt i ^^^ wt j) < 75735)

end CFSG.SmithD6
