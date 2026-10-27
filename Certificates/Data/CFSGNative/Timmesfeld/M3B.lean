module

public import Std.Data.HashMap

public section

set_option compiler.extract_closed false

namespace Timmesfeld.M3B

abbrev F3 := Fin 3

@[expose] def fsum (n : Nat) (f : Fin n → F3) : F3 := Fin.foldl n (fun s i => s + f i) 0

abbrev Vec := Array F3

@[expose] def vget (a : Vec) (i : Fin 12) : F3 := a[i.val]!

@[expose] def vofFn (f : Fin 12 → F3) : Vec := Array.ofFn f

@[expose] def zeroV : Vec := vofFn fun _ => 0

abbrev Mat := Array Vec

@[expose] def mget (A : Mat) (i j : Fin 12) : F3 := vget (A[i.val]!) j

@[expose] def mofFn (f : Fin 12 → Fin 12 → F3) : Mat := Array.ofFn fun i => vofFn (f i)

@[expose] def mmul (A B : Mat) : Mat := mofFn fun i j => fsum 12 fun k => mget A i k * mget B k j

@[expose] def mone : Mat := mofFn fun i j => if i = j then 1 else 0

@[expose] def meq (A B : Mat) : Bool :=
  (List.finRange 12).all fun i => (List.finRange 12).all fun j => mget A i j == mget B i j

@[expose] def mOfRows (R : List (List Nat)) : Mat :=
  mofFn fun i j => Fin.ofNat 3 ((R.getD i.val []).getD j.val 0)

abbrev E := Vec × F3

@[expose] def eone : E := (zeroV, 0)

@[expose] def beta (B : Mat) (a b : Vec) : F3 :=
  fsum 12 fun i => fsum 12 fun j => if j < i then vget a i * vget b j * mget B i j else 0

@[expose] def emul (B : Mat) (x y : E) : E :=
  (vofFn fun i => vget x.1 i + vget y.1 i, x.2 + y.2 + beta B x.1 y.1)

@[expose] def epow (B : Mat) (x : E) : Nat → E
  | 0 => eone
  | k + 1 => emul B (epow B x k) x

@[expose] def eprod (B : Mat) (l : List E) : E := l.foldl (emul B) eone

@[expose] def ecomm (B : Mat) (x y : E) : E :=
  emul B (emul B (emul B (epow B x 2) (epow B y 2)) x) y

@[expose] def eeq (x y : E) : Bool :=
  ((List.finRange 12).all fun i => vget x.1 i == vget y.1 i) && x.2 == y.2

abbrev AD := Array E × F3

@[expose] def aget (D : AD) (i : Fin 12) : E := D.1[i.val]!

@[expose] def subst (B : Mat) (D : AD) (x : E) : E :=
  emul B (eprod B (List.ofFn fun i => epow B (aget D i) (vget x.1 i).val)) (zeroV, D.2 * x.2)

@[expose] def comp (B : Mat) (D D' : AD) : AD :=
  (Array.ofFn (n := 12) fun i => subst B D' (aget D i), D.2 * D'.2)

@[expose] def adOne : AD :=
  (Array.ofFn (n := 12) fun i => (vofFn fun j => if i = j then 1 else 0, 0), 1)

@[expose] def adPow (B : Mat) (D : AD) : Nat → AD
  | 0 => adOne
  | k + 1 => comp B (adPow B D k) D

@[expose] def adEq (D D' : AD) : Bool :=
  ((List.finRange 12).all fun i => eeq (aget D i) (aget D' i)) && D.2 == D'.2

@[expose] def adOfRows (R : List (List Nat)) (c : List Nat) (lam : Nat) : AD :=
  let A := mOfRows R
  (Array.ofFn (n := 12) fun i => (A[i.val]!, Fin.ofNat 3 (c.getD i.val 0)), Fin.ofNat 3 lam)

@[expose] def adQ (B : Mat) (j : Fin 12) : AD :=
  (Array.ofFn (n := 12) fun i => (vofFn fun k => if i = k then 1 else 0, mget B i j), 1)

inductive WT where
  | gen (i : Nat)
  | mul (a b : WT)
  | pow (t : WT) (k : Nat)
  deriving Inhabited

@[expose] def adOf (B : Mat) (gens : Array AD) : WT → AD
  | .gen i => gens.getD i adOne
  | .mul a b => comp B (adOf B gens a) (adOf B gens b)
  | .pow t k => adPow B (adOf B gens t) k

@[expose] def WT.inv : WT → WT
  | .gen i => if i = 0 then .gen 2 else if i = 1 then .gen 3 else if i = 2 then .gen 0
      else if i = 3 then .gen 1 else .pow (.gen i) 2
  | .mul a b => .mul (WT.inv b) (WT.inv a)
  | .pow t k => .pow (WT.inv t) k

@[expose] def WT.zpow (t : WT) (k : Int) : WT :=
  if 0 ≤ k then .pow t k.toNat else .pow (WT.inv t) (-k).toNat

partial def readNat (cs : List Char) (acc : Nat) : Nat × List Char :=
  match cs with
  | c :: rest => if c.isDigit then readNat rest (10 * acc + (c.toNat - '0'.toNat)) else (acc, cs)
  | [] => (acc, [])

mutual
partial def parseAtom (cs : List Char) : WT × List Char :=
  let (base, rest) : WT × List Char :=
    match cs with
    | 'a' :: r => (.gen 0, r)
    | 'b' :: r => (.gen 1, r)
    | '(' :: r =>
      let (t, r') := parseProd r
      (t, match r' with | ')' :: r'' => r'' | _ => r')
    | _ => (.gen 0, [])
  parseExps base rest
partial def parseExps (t : WT) (cs : List Char) : WT × List Char :=
  match cs with
  | '^' :: '-' :: r => let (k, r') := readNat r 0; parseExps (WT.zpow t (-(k : Int))) r'
  | '^' :: r => let (k, r') := readNat r 0; parseExps (WT.zpow t k) r'
  | _ => (t, cs)
partial def parseProd (cs : List Char) : WT × List Char :=
  let (t, rest) := parseAtom cs
  parseMore t rest
partial def parseMore (t : WT) (cs : List Char) : WT × List Char :=
  match cs with
  | '*' :: r => let (u, r') := parseAtom r; parseMore (.mul t u) r'
  | _ => (t, cs)
end

@[expose] def parseWT (s : String) : WT := (parseProd (s.toList.filter (· ≠ ' '))).1

@[expose] def mpow (A : Mat) : Nat → Mat
  | 0 => mone
  | k + 1 => mmul (mpow A k) A

@[expose] def matOf (gens : Array Mat) : WT → Mat
  | .gen i => gens.getD i mone
  | .mul a b => mmul (matOf gens a) (matOf gens b)
  | .pow t k => mpow (matOf gens t) k

@[expose] def adMat (D : AD) : Mat := Array.ofFn (n := 12) fun i => (aget D i).1

@[expose] def unpack (p : Nat) : Vec := vofFn fun i => Fin.ofNat 3 (p / 3 ^ i.val)

@[expose] def ofDigits3 (ds : List Nat) : Nat := ds.foldr (fun d s => d + 3 * s) 0

@[expose] def pack (c : Vec) : Nat := ofDigits3 (List.ofFn fun i : Fin 12 => (vget c i).val)

@[expose] def fpt (T : Mat) (lam : F3) (c : Vec) : AD :=
  (Array.ofFn (n := 12) fun i => (T[i.val]!, vget c i), lam)

@[expose] def fimg0 (B T : Mat) (lam : F3) (G Gi : AD) : AD :=
  comp B (comp B Gi (fpt T lam zeroV)) G

@[expose] def fibreGenOK (B T : Mat) (lam : F3) (G Gi : AD) : Bool :=
  meq (adMat (fimg0 B T lam G Gi)) T && (fimg0 B T lam G Gi).2 == lam

@[expose] def affOf (B T : Mat) (lam : F3) (G Gi : AD) : Mat × Vec :=
  (mofFn fun j i => G.2 * vget (aget Gi i).1 j, vofFn fun i => (aget (fimg0 B T lam G Gi) i).2)

@[expose] def affApply (a : Mat × Vec) (p : Nat) : Nat :=
  let c := unpack p
  pack (vofFn fun i => fsum 12 (fun j => vget c j * mget a.1 j i) + vget a.2 i)

@[expose] def nPts : Nat := 3 ^ 12

@[expose] def fibreCheck (affs : Array (Mat × Vec)) (roots : List Nat) (par gen dist : Array Nat) :
    Bool :=
  par.size = nPts && gen.size = nPts && dist.size = nPts &&
  (List.range nPts).all fun p =>
    if dist[p]! = 0 then roots.contains p
    else gen[p]! < affs.size && affApply affs[gen[p]!]! p = par[p]! && par[p]! < nPts &&
      dist[par[p]!]! + 1 = dist[p]!

@[expose] def fibreBFS (affs : Array (Mat × Vec)) (roots : List Nat) (inv : Array Nat) :
    Array Nat × Array Nat × Array Nat := Id.run do
  let mut par : Array Nat := Array.replicate nPts nPts
  let mut gen : Array Nat := Array.replicate nPts 0
  let mut dist : Array Nat := Array.replicate nPts 0
  let mut queue : Array Nat := #[]
  for r in roots do
    if r < nPts && par[r]! = nPts then
      par := par.set! r r
      queue := queue.push r
  let mut head := 0
  for _ in [0:nPts] do
    if head < queue.size then
      let q := queue[head]!
      head := head + 1
      for k in [0:affs.size] do
        let p := affApply affs[k]! q
        if par[p]! = nPts then
          par := par.set! p q
          gen := gen.set! p (inv[k]!)
          dist := dist.set! p (dist[q]! + 1)
          queue := queue.push p
  return (par, gen, dist)

@[expose] def letterAD (B : Mat) (Da Db : AD) : Array AD := #[Da, Db, adPow B Da 55, adPow B Db 21]

@[expose] def mkey (A : Mat) : Array Nat := Array.ofFn (n := 12) fun i => pack (A[i.val]!)

@[expose] def cubeOne (A : Mat) : Bool := meq (mmul (mmul A A) A) mone

@[expose] def grpBFS (gens : Array Mat) (bound : Nat) : Array Mat × Array Nat × Array Nat :=
  Id.run do
  let mut elems : Array Mat := #[mone]
  let mut par : Array Nat := #[0]
  let mut gen : Array Nat := #[0]
  let mut idx : Std.HashMap (Array Nat) Nat :=
    (∅ : Std.HashMap (Array Nat) Nat).insert (mkey mone) 0
  let mut head := 0
  for _ in [0:bound] do
    if head < elems.size then
      let e := elems[head]!
      for k in [0:gens.size] do
        let f := mmul e gens[k]!
        let key := mkey f
        if !(idx.contains key) then
          idx := idx.insert key elems.size
          elems := elems.push f
          par := par.push head
          gen := gen.push k
      head := head + 1
  return (elems, par, gen)

@[expose] def keyMap (elems : Array Mat) : Std.HashMap (Array Nat) Nat :=
  (List.range elems.size).foldl (fun m i => m.insert (mkey elems[i]!) i) ∅

@[expose] def lookupIdx (m : Std.HashMap (Array Nat) Nat) (N : Nat) (A : Mat) : Nat :=
  (m.get? (mkey A)).getD N

@[expose] def grpCheck (gens : Array Mat) (elems : Array Mat) (par gen : Array Nat) : Bool :=
  let N := elems.size
  let m := keyMap elems
  par.size = N && gen.size = N && 0 < N && meq elems[0]! mone &&
  (List.range N).all (fun i => i = 0 ||
    (par[i]! < i && gen[i]! < gens.size && meq elems[i]! (mmul elems[par[i]!]! gens[gen[i]!]!))) &&
  (List.range N).all (fun i => lookupIdx m N elems[i]! = i) &&
  (List.range N).all (fun i => (List.range gens.size).all fun k =>
    let f := mmul elems[i]! gens[k]!
    lookupIdx m N f < N && meq elems[lookupIdx m N f]! f)

@[expose] def conjBFS (gens : Array Mat) (inv : Array Nat) (elems : Array Mat) (roots : List Nat) :
    Array Nat × Array Nat × Array Nat := Id.run do
  let N := elems.size
  let m := keyMap elems
  let mut par : Array Nat := Array.replicate N N
  let mut gen : Array Nat := Array.replicate N 0
  let mut dist : Array Nat := Array.replicate N 0
  let mut queue : Array Nat := #[]
  for r in roots do
    if r < N && par[r]! = N then
      par := par.set! r r
      queue := queue.push r
  let mut head := 0
  for _ in [0:N] do
    if head < queue.size then
      let q := queue[head]!
      head := head + 1
      for k in [0:gens.size] do
        let f := mmul (mmul gens[k]! elems[q]!) gens[inv[k]!]!
        let j := lookupIdx m N f
        if j < N && par[j]! = N then
          par := par.set! j q
          gen := gen.set! j k
          dist := dist.set! j (dist[q]! + 1)
          queue := queue.push j
  return (par, gen, dist)

@[expose] def conjCheck (gens : Array Mat) (elems : Array Mat) (roots : List Nat)
    (par gen dist : Array Nat) : Bool :=
  let N := elems.size
  par.size = N && gen.size = N && dist.size = N &&
  (List.range N).all fun i =>
    if cubeOne elems[i]! && !(meq elems[i]! mone) then
      if dist[i]! = 0 then roots.contains i
      else par[i]! < N && gen[i]! < gens.size &&
        meq (mmul elems[i]! gens[gen[i]!]!) (mmul gens[gen[i]!]! elems[par[i]!]!) &&
        dist[par[i]!]! + 1 = dist[i]!
    else true

@[expose] def eOf (v : List Nat) (e : Nat) : E :=
  (vofFn fun i => Fin.ofNat 3 (v.getD i.val 0), Fin.ofNat 3 e)

@[expose] def ebasis (i : Fin 12) : E := (vofFn fun j => if i = j then 1 else 0, 0)

@[expose] def nfD (B : Mat) (x : E) : AD :=
  (Array.ofFn (n := 12) fun i => emul B (emul B (epow B x 2) (ebasis i)) x, 1)

@[expose] def cubeE (B : Mat) (D : AD) (x : E) : E :=
  emul B (emul B (subst B D (subst B D x)) (subst B D x)) x

@[expose] def zconjE (B : Mat) (D : AD) (x y : E) : E :=
  emul B (emul B (subst B D (epow B y 2)) x) y

@[expose] def qword (v : List Nat) : WT :=
  (List.range 12).foldl (fun t i => .mul t (.pow (.gen (4 + i)) (v.getD i 0))) (.pow (.gen 4) 0)

@[expose] def ptOf (D : AD) : Nat := pack (vofFn fun i => (aget D i).2)

@[expose] def fibreAffs (B T : Mat) (lam : F3) (gd : Array (AD × AD)) : Array (Mat × Vec) :=
  gd.foldl (fun acc (G, Gi) => (acc.push (affOf B T lam G Gi)).push (affOf B T lam Gi G)) #[]

@[expose] def fibreGensOK (B T : Mat) (lam : F3) (gd : Array (AD × AD)) : Bool :=
  gd.all fun (G, Gi) => adEq (comp B Gi G) adOne && adEq (comp B G Gi) adOne &&
    fibreGenOK B T lam G Gi && fibreGenOK B T lam Gi G

@[expose] def fibreFull (B T : Mat) (lam : F3) (gd : Array (AD × AD)) (roots : List AD) : Bool :=
  let affs := fibreAffs B T lam gd
  let inv := (List.range affs.size).toArray.map fun i => if i % 2 = 0 then i + 1 else i - 1
  let rp := roots.map ptOf
  let F := fibreBFS affs rp inv
  fibreGensOK B T lam gd && roots.all (fun D => meq (adMat D) T && D.2 == lam) &&
    fibreCheck affs rp F.1 F.2.1 F.2.2

@[expose] def mRows : List (List Nat) :=
  [[0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [1, 0, 0, 2, 0, 1, 2, 2, 0, 2, 2, 1],
    [0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0],
    [0, 1, 0, 0, 0, 0, 0, 1, 2, 0, 2, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0],
    [0, 2, 0, 0, 0, 0, 0, 2, 2, 1, 1, 0],
    [0, 1, 0, 0, 0, 0, 0, 2, 2, 0, 2, 1],
    [0, 1, 2, 2, 0, 1, 1, 0, 0, 1, 0, 0],
    [0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0],
    [0, 1, 2, 0, 1, 2, 0, 2, 0, 0, 2, 1],
    [0, 1, 0, 1, 0, 2, 1, 0, 0, 1, 0, 0],
    [0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0]]

@[expose] def xRows : List (List Nat) :=
  [[0, 2, 2, 2, 1, 2, 2, 0, 2, 2, 2, 1],
    [1, 0, 0, 2, 2, 1, 0, 0, 2, 0, 0, 2],
    [2, 2, 2, 0, 2, 2, 1, 1, 2, 2, 1, 2],
    [0, 0, 2, 1, 0, 2, 0, 0, 2, 1, 2, 1],
    [0, 1, 1, 1, 2, 2, 1, 1, 0, 0, 2, 2],
    [0, 1, 1, 0, 2, 0, 1, 0, 0, 2, 2, 0],
    [2, 1, 2, 1, 2, 0, 0, 1, 1, 1, 0, 2],
    [2, 1, 1, 2, 1, 0, 1, 2, 2, 0, 0, 2],
    [0, 0, 1, 2, 0, 1, 0, 2, 1, 0, 2, 1],
    [0, 2, 2, 2, 2, 1, 2, 1, 1, 0, 2, 0],
    [2, 2, 2, 1, 1, 1, 2, 2, 0, 2, 1, 2],
    [0, 2, 2, 1, 1, 0, 2, 2, 0, 1, 1, 2]]

@[expose] def xiRows : List (List Nat) :=
  [[1, 2, 1, 0, 0, 1, 2, 0, 1, 1, 1, 2],
    [2, 2, 2, 2, 0, 1, 2, 0, 2, 1, 1, 2],
    [1, 1, 0, 0, 0, 2, 0, 1, 1, 2, 0, 0],
    [2, 2, 2, 2, 2, 2, 1, 0, 1, 0, 2, 2],
    [2, 2, 1, 2, 1, 2, 2, 1, 0, 0, 1, 2],
    [1, 0, 1, 0, 0, 0, 2, 1, 1, 0, 2, 2],
    [1, 1, 1, 0, 0, 1, 1, 0, 2, 0, 2, 1],
    [2, 2, 2, 0, 2, 0, 1, 1, 2, 1, 1, 1],
    [1, 0, 2, 0, 0, 2, 1, 1, 2, 2, 2, 0],
    [0, 2, 0, 0, 0, 1, 0, 2, 0, 1, 0, 2],
    [2, 0, 2, 0, 2, 0, 1, 1, 2, 2, 2, 2],
    [0, 0, 0, 2, 0, 1, 0, 2, 2, 2, 1, 0]]

@[expose] def yRows : List (List Nat) :=
  [[2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [1, 2, 2, 0, 0, 1, 2, 0, 1, 0, 0, 0],
    [2, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0],
    [2, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0],
    [1, 0, 0, 1, 2, 2, 1, 0, 0, 0, 0, 0],
    [0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 0, 0],
    [1, 0, 1, 2, 2, 0, 1, 0, 0, 0, 0, 0],
    [2, 0, 0, 2, 1, 1, 0, 1, 1, 0, 2, 0],
    [2, 0, 1, 0, 0, 1, 2, 0, 0, 1, 1, 0],
    [2, 0, 2, 0, 2, 1, 0, 2, 0, 1, 2, 0],
    [0, 0, 1, 2, 2, 1, 1, 0, 2, 0, 1, 2],
    [2, 0, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1]]

@[expose] def yiRows : List (List Nat) :=
  [[2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 2, 2, 0, 0, 0, 1, 1, 2, 1, 0, 0],
    [0, 0, 1, 1, 2, 1, 0, 0, 0, 0, 0, 0],
    [2, 0, 0, 1, 2, 2, 1, 0, 0, 0, 0, 0],
    [0, 0, 2, 1, 2, 2, 1, 0, 0, 0, 0, 0],
    [1, 0, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 1, 1, 2, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 2, 1, 2, 2, 2, 2, 2, 1, 1],
    [0, 0, 2, 1, 0, 1, 1, 1, 2, 1, 0, 0],
    [1, 0, 1, 1, 0, 2, 0, 1, 0, 0, 2, 2],
    [0, 0, 0, 1, 2, 0, 0, 2, 1, 0, 1, 1],
    [2, 0, 0, 1, 0, 2, 0, 1, 2, 2, 0, 1]]

@[expose] def c1 : List Nat := [2, 1, 1, 0, 2, 1, 1, 0, 1, 2, 2, 0]

@[expose] def c2 : List Nat := [0, 2, 0, 1, 0, 0, 0, 1, 1, 1, 2, 2]

@[expose] def sigW : Array WT :=
  #[.pow (.mul (.gen 0) (.pow (.gen 3) 2)) 8, .pow (.mul (.pow (.gen 0) 2) (.pow (.gen 3) 2)) 8,
    .pow (.mul (.pow (.gen 0) 3) (.gen 1)) 8]

@[expose] def cent1 : List String :=
  ["(b*a)^3*a*b*(b^2*a)^2*a^2*(a*b)^4*b^2*a*b^3*a*(a*b)^2*b*a^3*b^5*(b*a)^7*b^2*(b*a*b^5*(b*\
    a)^7)^2*b^2*((b^5*a*b)^2*(a*b)^5*a)^2*b^-4*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5\
    *(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4*a^2*b*a^3*b^7*(a*b*a)^2*b^2*a*(\
    a*b^5*(b*a)^7*b)^2*b*(b^2*(b*a*b^5*(b*a)^7)^2)^2*b^3*a*b^5*(b*a)^7)^2*b^-1",
   "b^2*a^3*(b*a*b^2)^2*a*b*(b*a)^2*(b*a*b^2)^2*b*a*(a*b)^2*b*a^3*b^5*(b*a)^7*b^8*(b*a*b^5*(\
    b*a)^7)^4*b^5*(b*a)^3*a*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2\
    *b^11*a*b^5*(b*a)^7*b^-4*a^2*b*a^3*b^7*(a*b*a)^2*b^2*a*(a*b^5*(b*a)^7*b)^2*b*(b^2*(b*a*b\
    ^5*(b*a)^7)^2)^2*b^3*a*b^5*(b*a)^7*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7\
    *b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^5*b^-1*(a*b)^2*a^2*b^4*a^3*b^2*a*b*a^-\
    1*(b*a)^2*(b*a*b^2)^2*b*a*(a*b)^2*b*a^3*b^5*(b*a)^7*b^2*(b*a*b^5*(b*a)^7)^3*b^4*(b*a*b^5\
    *(b*a)^7)^5*b^8*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)\
    ^7)^2*b^11*a*b^5*(b*a)^7*b^-4*a^2*b*a^3*b^7*(a*b*a)^2*b^2*a*(a*b^5*(b*a)^7*b)^2*b*(b^2*(\
    b*a*b^5*(b*a)^7)^2)^2*b^3*a*b^5*(b*a)^7*(a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*\
    a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^2*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3\
    *a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^6*b^-1"]

@[expose] def cent2 : List String :=
  ["b^5*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^\
    -6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2*a^-1*b^4*(a^-1*b^-1)^7*b^\
    -5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*\
    (b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2*((a^-1*b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^\
    -1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3\
    *b^-4*a^-1*(a^-1*b^-1)^2)^3*a^-1*((a^-1*b^-1)^7*b^-5*a^-1*b^-2*(b^-1*a^-1)^7*b^-6*a^-1*b\
    ^-1)^2*(a^-1*b^-1)^7*b^-5*a^-1*b^-4*((b^-1*a^-1)^7*b^-6*a^-1)^2*a^-1*b^-2*(a^-1*b^-1*a^-\
    1)^2*b^-7*a^-3*b^-1*a^-1)^2*a^-1*b^-1*(b^-1*a^-1)^7*b^-6*a^-1*b^-2*(b^-2*((b^-1*a^-1)^7*\
    b^-6*a^-1)^2)^2*((b^-1*a^-1)^7*b^-6*a^-1)^3*a^-2*b^-1*(b^-1*a^-1)^2*(a^-1*b^-3)^2*(a^-1*\
    b^-1)^4*b^-1*a^-1*b^-2*a^-2*b^-2*(b^-3*a^-1)^2*b^-1*(b^-1*a^-1*b^4*(a^-1*b^-1)^7*b^-5*a^\
    -1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*(b^-1\
    *a^-1)^2*a^-3*b^-4*a^-2*b^-1*a^-1)^3*b^-1*(a^-1*((a^-1*b^-1)^7*b^-5*a^-1*b^-2*(b^-1*a^-1\
    )^7*b^-6*a^-1*b^-1)^2*(a^-1*b^-1)^7*b^-5*a^-1*b^-4*((b^-1*a^-1)^7*b^-6*a^-1)^2*a^-1*b^-2\
    *(a^-1*b^-1*a^-1)^2*b^-7*a^-3*b^-1*a^-1)^3*a^-1*b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^-1\
    *b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3*b\
    ^-4*a^-1*(a^-1*b^-1)^2*a^-1*((a^-1*b^-1)^7*b^-5*a^-1*b^-2*(b^-1*a^-1)^7*b^-6*a^-1*b^-1)^\
    2*(a^-1*b^-1)^7*b^-5*a^-1*b^-4*((b^-1*a^-1)^7*b^-6*a^-1)^2*a^-1*b^-2*(a^-1*b^-1*a^-1)^2*\
    b^-7*a^-3*b^-1*a^-2*b^8*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^3*b^-1*(b^-2*(b^-1*a^-1)^7*b^-6*a\
    ^-1)^2*(b^-1*a^-1)^6*(b^-1*a^-1*b^-5)^2*(b^-1*a^-3)^2*b^-2*a^-4*b^-1*a^-2",
   "b^5*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^\
    -6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2*a^-1*b^4*(a^-1*b^-1)^7*b^\
    -5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*\
    (b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2*((a^-1*b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^\
    -1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3\
    *b^-4*a^-1*(a^-1*b^-1)^2)^3*a^-1*((a^-1*b^-1)^7*b^-5*a^-1*b^-2*(b^-1*a^-1)^7*b^-6*a^-1*b\
    ^-1)^2*(a^-1*b^-1)^7*b^-5*a^-1*b^-4*((b^-1*a^-1)^7*b^-6*a^-1)^2*a^-1*b^-2*(a^-1*b^-1*a^-\
    1)^2*b^-7*a^-3*b^-1*a^-1)^2*a^-1*b^-1*(b^-1*a^-1)^7*b^-6*a^-1*b^-2*(b^-2*((b^-1*a^-1)^7*\
    b^-6*a^-1)^2)^2*((b^-1*a^-1)^7*b^-6*a^-1)^3*a^-2*b^-1*(b^-1*a^-1)^2*(a^-1*b^-3)^2*(a^-1*\
    b^-1)^4*b^-1*a^-1*b^-2*a^-2*b^-2*(b^-3*a^-1)^2*b^-1*(b^-1*a^-1*b^4*(a^-1*b^-1)^7*b^-5*a^\
    -1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*(b^-1\
    *a^-1)^2*a^-3*b^-4*a^-2*b^-1*a^-1)^8*b^-1*a^-1*((a^-1*b^-1)^7*b^-5*a^-1*b^-2*(b^-1*a^-1)\
    ^7*b^-6*a^-1*b^-1)^2*(a^-1*b^-1)^7*b^-5*a^-1*b^-4*((b^-1*a^-1)^7*b^-6*a^-1)^2*a^-1*b^-2*\
    (a^-1*b^-1*a^-1)^2*b^-7*a^-3*b^-1*a^-1*(a^-1*b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^-1*b^\
    -1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3*b^-4\
    *a^-1*(a^-1*b^-1)^2)^2*a^-1*(b^-1*((b^-1*a^-1)^7*b^-6*a^-1)^2*b^-5)^2*b^-1*((b^-1*a^-1)^\
    7*b^-6*a^-1)^2*a^-2*b^-1*(b^-1*a^-1)^2*(a^-1*b^-3)^2*(a^-1*b^-1)^3*a^-4*(a^-3*b^-1)^2*b^\
    -1*a^-1*b^-2*a^-2",
   "b^5*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^\
    -6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2*a^-1*b^4*(a^-1*b^-1)^7*b^\
    -5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*\
    (b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2*((a^-1*b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^\
    -1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3\
    *b^-4*a^-1*(a^-1*b^-1)^2)^3*a^-1*((a^-1*b^-1)^7*b^-5*a^-1*b^-2*(b^-1*a^-1)^7*b^-6*a^-1*b\
    ^-1)^2*(a^-1*b^-1)^7*b^-5*a^-1*b^-4*((b^-1*a^-1)^7*b^-6*a^-1)^2*a^-1*b^-2*(a^-1*b^-1*a^-\
    1)^2*b^-7*a^-3*b^-1*a^-1)^2*a^-1*b^-1*(b^-1*a^-1)^7*b^-6*a^-1*b^-2*(b^-2*((b^-1*a^-1)^7*\
    b^-6*a^-1)^2)^2*((b^-1*a^-1)^7*b^-6*a^-1)^3*a^-2*b^-1*(b^-1*a^-1)^2*(a^-1*b^-3)^2*(a^-1*\
    b^-1)^4*b^-1*a^-1*b^-2*a^-2*b^-2*(b^-3*a^-1)^2*b^-1*(b^-1*a^-1*b^4*(a^-1*b^-1)^7*b^-5*a^\
    -1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*(b^-1\
    *a^-1)^2*a^-3*b^-4*a^-2*b^-1*a^-1)^5*b^-1*(a^-1*((a^-1*b^-1)^7*b^-5*a^-1*b^-2*(b^-1*a^-1\
    )^7*b^-6*a^-1*b^-1)^2*(a^-1*b^-1)^7*b^-5*a^-1*b^-4*((b^-1*a^-1)^7*b^-6*a^-1)^2*a^-1*b^-2\
    *(a^-1*b^-1*a^-1)^2*b^-7*a^-3*b^-1*a^-1)^2*a^-1*b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^-1\
    *b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3*b\
    ^-4*a^-1*(a^-1*b^-1)^2*a^-1*b^-12*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^4*b^-1*((b^-1*a^-1)^7*b\
    ^-6*a^-1)^3*a^-1*b^-1*a^-1*(b^-1*a^-2*b^-1)^2*b^-1*a^-1*b^-2"]

@[expose] def cent3 : List String :=
  ["(b*a^3)^2*a^3*b^3*a^2*(a*b)^4*b^2*a*b^3*a*(a*b)^2*b*a^2*b^3*(b^4*(b*a*b^5*(b*a)^7)^2)^2*\
    b*a*b^5*(b*a)^7*(a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^\
    7)^2*b^11*a*b^5*(b*a)^7*b^-4*(a^2*b*a^3*b^7*(a*b*a)^2*b^2*a*(a*b^5*(b*a)^7*b)^2*b*(b^2*(\
    b*a*b^5*(b*a)^7)^2)^2*b^3*a*b^5*(b*a)^7)^3*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5\
    *(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^3*a*(b^2*a*b)^2*b^4*a^2*b^2*a*\
    b*(b*a)^4*(b^3*a)^2*(a*b)^2*b*a^2*(a*b^5*(b*a)^7*b)^2*a*b^5*(b*a)^7*((b*a*b^5*(b*a)^7)^2\
    *b^2)^2*b^3*a*b^5*(b*a)^7*b^2*(a^2*b*a^3*b^7*(a*b*a)^2*b^2*a*(a*b^5*(b*a)^7*b)^2*b*(b^2*\
    (b*a*b^5*(b*a)^7)^2)^2*b^3*a*b^5*(b*a)^7*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(\
    b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^3)^2*((a*b)^2*a^2*b^4*a^3*(a*b)^\
    2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^2*b^-1",
   "a^3*b*(b^2*a)^3*b*a*(b*a*b^2)^2*b*a*(a*b)^2*b*a^2*(a*b^5*(b*a)^7*b)^2*b^5*(b*a*b^5*(b*a)\
    ^7)^5*(b^5*a*b)^2*(a*b)^6*b^3*(a^2*b*a^3*b^7*(a*b*a)^2*b^2*a*(a*b^5*(b*a)^7*b)^2*b*(b^2*\
    (b*a*b^5*(b*a)^7)^2)^2*b^3*a*b^5*(b*a)^7)^3*(a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5\
    *(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4*a^2*b*a^3*b^7*(a*b*a)^2*b^2*a*(\
    a*b^5*(b*a)^7*b)^2*b*(b^2*(b*a*b^5*(b*a)^7)^2)^2*b^3*a*b^5*(b*a)^7*((a*b)^2*a^2*b^4*a^3*\
    (a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^10*b^-\
    1"]

@[expose] def sylGens : List String :=
  ["b*(b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7\
    *b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2*a^-1)^5*((a^-1*b^-1)^7\
    *b^-5*a^-1*b^-2*(b^-1*a^-1)^7*b^-6*a^-1*b^-1)^2*(a^-1*b^-1)^7*b^-5*a^-1*b^-4*((b^-1*a^-1\
    )^7*b^-6*a^-1)^2*a^-1*b^-2*(a^-1*b^-1*a^-1)^2*b^-7*a^-3*b^-1*a^-1*(a^-1*b^4*(a^-1*b^-1)^\
    7*b^-5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b\
    ^-3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2)^3*a^-1*b^-5*(b^-2*(b^-1*a^-1)^7*b^-6*a^-\
    1)^2*b^-2*(b^-2*((b^-1*a^-1)^7*b^-6*a^-1)^2)^2*b^-2*(b^-1*a^-1)^7*b^-5*(b^-1*a^-1)^2*b^-\
    1*(a^-1*b^-1*a^-3)^2*b^-1*a^-1",
   "a^4*b^2*a*(a^2*b)^2*a^3*b*(b*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2)^2*(b^-2*(a*b)^2*a^2*\
    b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-2\
    )^2*b^-2*(a^2*b*a^3*b^7*(a*b*a)^2*b^2*a*(a*b^5*(b*a)^7*b)^2*b*(b^2*(b*a*b^5*(b*a)^7)^2)^\
    2*b^3*a*b^5*(b*a)^7)^2*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^\
    5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^2*b^-1*(a*b)^2*a^2*b^4*a^3*b^2*a*b*a^-1*(b*a)^2*(b\
    *a*b^2)^2*b*a*(a*b)^2*b*a^3*b^5*(b*a)^7*b^2*(b*a*b^5*(b*a)^7)^3*b^4*(b*a*b^5*(b*a)^7)^5*\
    b^8*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a\
    *b^5*(b*a)^7*b^-4*a^2*b*a^3*b^7*(a*b*a)^2*b^2*a*(a*b^5*(b*a)^7*b)^2*b*(b^2*(b*a*b^5*(b*a\
    )^7)^2)^2*b^3*a*b^5*(b*a)^7*(a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*\
    a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^2*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^\
    5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^6*b^-1",
   "b^5*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^\
    -6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2*a^-1*b^4*(a^-1*b^-1)^7*b^\
    -5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*\
    (b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2*((a^-1*b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^\
    -1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3\
    *b^-4*a^-1*(a^-1*b^-1)^2)^3*a^-1*((a^-1*b^-1)^7*b^-5*a^-1*b^-2*(b^-1*a^-1)^7*b^-6*a^-1*b\
    ^-1)^2*(a^-1*b^-1)^7*b^-5*a^-1*b^-4*((b^-1*a^-1)^7*b^-6*a^-1)^2*a^-1*b^-2*(a^-1*b^-1*a^-\
    1)^2*b^-7*a^-3*b^-1*a^-1)^2*a^-1*b^-1*(b^-1*a^-1)^7*b^-6*a^-1*b^-2*(b^-2*((b^-1*a^-1)^7*\
    b^-6*a^-1)^2)^2*((b^-1*a^-1)^7*b^-6*a^-1)^3*a^-2*b^-1*(b^-1*a^-1)^2*(a^-1*b^-3)^2*(a^-1*\
    b^-1)^4*b^-1*a^-1*b^-2*a^-2*b^-2*(b^-3*a^-1)^2*b^-2*(a^-1*b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^\
    -11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1\
    )^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2*a^-1*((a^-1*b^-1)^7*b^-5*a^-1*b^-2*(b^-1*a^-1)^7*b^-6*a\
    ^-1*b^-1)^2*(a^-1*b^-1)^7*b^-5*a^-1*b^-4*((b^-1*a^-1)^7*b^-6*a^-1)^2*a^-1*b^-2*(a^-1*b^-\
    1*a^-1)^2*b^-7*a^-3*b^-1*a^-1)^2*a^-1*b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^-1*b^-1)^7*b\
    ^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*(\
    a^-1*b^-1)^3*(b^-1*a^-1)^7*b^-6*a^-1*b^-4*((b^-1*a^-1)^7*b^-6*a^-1)^3*b^-12*a^-2*b^-6*a^\
    -4*b^-2",
   "(a*b*a)^2*b*(a^3*b^2*a)^2*b*a*(b*a*b^2)^2*b*a*(a*b)^2*b*a*(a*b^4)^2*b*(b*a)^7*((b^5*a*b)\
    ^2*(a*b)^6*b^3)^2*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*\
    a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^7*b^-1",
   "b*((a^-1*b^-1)^7*b^-5*a^-1*b^-2*(b^-1*a^-1)^7*b^-6*a^-1*b^-1)^2*(a^-1*b^-1)^7*b^-5*a^-1*\
    b^-4*((b^-1*a^-1)^7*b^-6*a^-1)^2*a^-1*b^-2*(a^-1*b^-1*a^-1)^2*b^-7*a^-3*b^-1*a^-2*b^4*(a\
    ^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-\
    1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2*a^-1*b^6*((a^-1*b^-1)^7*b^-5*a^\
    -1*b^-1)^5*b^-1*(b^-2*(b^-1*a^-1)^7*b^-6*a^-1)^2*b^-3*a^-3*b^-2*a^-1*(a^-1*b^-1)^3*a^-1",
   "(a*b^4)^2*b^3*a^2*(a*b)^4*b^2*a*b^3*a*(a*b)^2*b*a^2*b*(b*a*b^5*(b*a)^7)^2*(b*a*b^5*(b*a)\
    ^7*b^2)^2*(b^2*(b*a*b^5*(b*a)^7)^2*b^3*a*b^5*(b*a)^7*(a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b\
    ^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4*a^2*b*a^3*b^7*(a*b*a)^\
    2*b^2*a*(a*b^5*(b*a)^7*b)^2*b^3*(b*a*b^5*(b*a)^7)^2)^2*b^2*(b*a*b^5*(b*a)^7)^2*b^3*a*b^5\
    *(b*a)^7*(a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^\
    11*a*b^5*(b*a)^7*b^-5*(a*b)^2*a^2*b^4*a^3*b^2*a*b*a^-1*(b*a)^2*(b*a*b^2)^2*b*a*(a*b)^2*b\
    *a^3*b^5*(b*a)^7*b^2*(b*a*b^5*(b*a)^7)^3*b^4*(b*a*b^5*(b*a)^7)^5*b^8*((a*b)^2*a^2*b^4*a^\
    3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4*a^2*b\
    *a^3*b^7*(a*b*a)^2*b^2*a*(a*b^5*(b*a)^7*b)^2*b*(b^2*(b*a*b^5*(b*a)^7)^2)^2*b^3*a*b^5*(b*\
    a)^7*(a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a\
    *b^5*(b*a)^7*b^-4)^2*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*\
    (b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^6*a*(b^2*a*b)^2*b^4*a^2*b^2*a*b*(b*a)^4*(b^3*a)^2*(a\
    *b)^2*b*a^2*(a*b^5*(b*a)^7*b)^2*a*b^5*(b*a)^7*((b*a*b^5*(b*a)^7)^2*b^2)^2*b^3*a*b^5*(b*a\
    )^7*b^2*(a^2*b*a^3*b^7*(a*b*a)^2*b^2*a*(a*b^5*(b*a)^7*b)^2*b*(b^2*(b*a*b^5*(b*a)^7)^2)^2\
    *b^3*a*b^5*(b*a)^7*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b\
    *a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^3)^2*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*\
    a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^2*b^-1",
   "a*b*a^4*(a*(a*b)^3)^2*(a*b^3)^2*a*(a*b)^2*b*a^2*(b^2*a*b^5*(b*a)^7*b)^2*b^3*(b*a*b^5*(b*\
    a)^7)^3*(b^5*a*b)^2*(a*b)^5*a*b^10*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7\
    *b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4*a^2*b*a^3*b^7*(a*b*a)^2*b^2*a*(a*b^5*(b\
    *a)^7*b)^2*b*(b^2*(b*a*b^5*(b*a)^7)^2)^2*b^3*a*b^5*(b*a)^7)^2*((a*b)^2*a^2*b^4*a^3*(a*b)\
    ^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^8*b^-1*(a*b\
    )^2*a^2*b^4*a^3*b^2*a*b*a^-1*(b*a)^2*(b*a*b^2)^2*b*a*(a*b)^2*b*a^3*b^5*(b*a)^7*b^2*(b*a*\
    b^5*(b*a)^7)^3*b^4*(b*a*b^5*(b*a)^7)^5*b^8*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5\
    *(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4*a^2*b*a^3*b^7*(a*b*a)^2*b^2*a*(\
    a*b^5*(b*a)^7*b)^2*b*(b^2*(b*a*b^5*(b*a)^7)^2)^2*b^3*a*b^5*(b*a)^7*(a*b)^2*a^2*b^4*a^3*(\
    a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^2*((a*b\
    )^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a\
    )^7*b^-4)^6*b^-1"]

@[expose] def conjData : List (Nat × String × String) :=
  [(0, "b^5*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^\
    -6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2*a^-1*b^4*(a^-1*b^-1)^7*b^\
    -5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*\
    (b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2*((a^-1*b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^\
    -1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3\
    *b^-4*a^-1*(a^-1*b^-1)^2)^3*a^-1*((a^-1*b^-1)^7*b^-5*a^-1*b^-2*(b^-1*a^-1)^7*b^-6*a^-1*b\
    ^-1)^2*(a^-1*b^-1)^7*b^-5*a^-1*b^-4*((b^-1*a^-1)^7*b^-6*a^-1)^2*a^-1*b^-2*(a^-1*b^-1*a^-\
    1)^2*b^-7*a^-3*b^-1*a^-1)^2*a^-1*b^-1*(b^-1*a^-1)^7*b^-6*a^-1*b^-2*(b^-2*((b^-1*a^-1)^7*\
    b^-6*a^-1)^2)^2*((b^-1*a^-1)^7*b^-6*a^-1)^3*a^-2*b^-1*(b^-1*a^-1)^2*(a^-1*b^-3)^2*(a^-1*\
    b^-1)^4*b^-1*a^-1*b^-2*a^-2*b^-2*(b^-3*a^-1)^2*b^-1*(b^-1*a^-1*b^4*(a^-1*b^-1)^7*b^-5*a^\
    -1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*(b^-1\
    *a^-1)^2*a^-3*b^-4*a^-2*b^-1*a^-1)^5*b^-1*((a^-1*b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^-\
    1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3*\
    b^-4*a^-1*(a^-1*b^-1)^2)^2*a^-1*((a^-1*b^-1)^7*b^-5*a^-1*b^-2*(b^-1*a^-1)^7*b^-6*a^-1*b^\
    -1)^2*(a^-1*b^-1)^7*b^-5*a^-1*b^-4*((b^-1*a^-1)^7*b^-6*a^-1)^2*a^-1*b^-2*(a^-1*b^-1*a^-1\
    )^2*b^-7*a^-3*b^-1*a^-1)^2*a^-1*b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^\
    -1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b\
    ^-1)^3*b^-6*((b^-1*a^-1)^7*b^-6*a^-1)^5*b^-4*((b^-1*a^-1)^7*b^-6*a^-1)^3*b^-2*(b^-1*a^-1\
    )^7*b^-6*a^-3*b^-1*(b^-1*a^-1)^2*(a^-1*b^-3)^2*(a^-1*b^-1)^3*a*b^-1*a^-1*b^-2*a^-3*b^-4*\
    a^-1*(a^-1*b^-1)^2*a^-1*b*(b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^\
    -1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^\
    2*a^-1*((a^-1*b^-1)^7*b^-5*a^-1*b^-2*(b^-1*a^-1)^7*b^-6*a^-1*b^-1)^2*(a^-1*b^-1)^7*b^-5*\
    a^-1*b^-4*((b^-1*a^-1)^7*b^-6*a^-1)^2*a^-1*b^-2*(a^-1*b^-1*a^-1)^2*b^-7*a^-3*b^-1*a^-2)^\
    2*b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*\
    b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2*a^-1*(a^-1*b^-1)^7*b^-5\
    *a^-1*b^-2*((b^-1*a^-1)^7*b^-6*a^-1)^2*b^-2*(b^-2*(b^-1*a^-1)^7*b^-6*a^-1)^2*((b^-1*a^-1\
    )^7*b^-6*a^-1)^2*b^-2*a^-2*b^-1*(b^-1*a^-1)^2*(a^-1*b^-3)^2*(a^-1*b^-1)^3*a^-3*b^-3*(b^-\
    4*a^-1)^2",
    "b*(b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7\
    *b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2*a^-1)^4*((a^-1*b^-1)^7\
    *b^-5*a^-1*b^-2*(b^-1*a^-1)^7*b^-6*a^-1*b^-1)^2*(a^-1*b^-1)^7*b^-5*a^-1*b^-4*((b^-1*a^-1\
    )^7*b^-6*a^-1)^2*a^-1*b^-2*(a^-1*b^-1*a^-1)^2*b^-7*a^-3*b^-1*a^-2*b^4*(a^-1*b^-1)^7*b^-5\
    *a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*(b\
    ^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^3*(b^-1*a^-1)^7*b^-6*a^-1*(b^-2*((b^-1*a^-1)^7*b^\
    -6*a^-1)^3*b^-2)^2*a^-2*b^-1*(b^-1*a^-1)^2*(a^-1*b^-3)^2*(a^-1*b^-1)^3*a^-2*(a^-2*b^-2)^\
    2*b^-1*a^-1*b^-3"),
   (0, "(a*b^4)^2*b^3*a^2*(a*b)^4*b^2*a*b^3*a*(a*b)^2*b*a^2*b*(b*a*b^5*(b*a)^7)^2*(b*a*b^5*(b*a)\
    ^7*b^2)^2*(b^2*(b*a*b^5*(b*a)^7)^2*b^3*a*b^5*(b*a)^7*(a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b\
    ^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4*a^2*b*a^3*b^7*(a*b*a)^\
    2*b^2*a*(a*b^5*(b*a)^7*b)^2*b^3*(b*a*b^5*(b*a)^7)^2)^2*b^2*(b*a*b^5*(b*a)^7)^2*b^3*a*b^5\
    *(b*a)^7*(a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^\
    11*a*b^5*(b*a)^7*b^-5*(a*b)^2*a^2*b^4*a^3*b^2*a*b*a^-1*(b*a)^2*(b*a*b^2)^2*b*a*(a*b)^2*b\
    *a^3*b^5*(b*a)^7*b^2*(b*a*b^5*(b*a)^7)^3*b^4*(b*a*b^5*(b*a)^7)^5*b^8*((a*b)^2*a^2*b^4*a^\
    3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4*a^2*b\
    *a^3*b^7*(a*b*a)^2*b^2*a*(a*b^5*(b*a)^7*b)^2*b*(b^2*(b*a*b^5*(b*a)^7)^2)^2*b^3*a*b^5*(b*\
    a)^7*(a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a\
    *b^5*(b*a)^7*b^-4)^2*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*\
    (b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^6*a*(b^2*a*b)^2*b^4*a^2*b^2*a*b*(b*a)^4*(b^3*a)^2*(a\
    *b)^2*b*a^2*(a*b^5*(b*a)^7*b)^2*a*b^5*(b*a)^7*((b*a*b^5*(b*a)^7)^2*b^2)^2*b^3*a*b^5*(b*a\
    )^7*b^2*(a^2*b*a^3*b^7*(a*b*a)^2*b^2*a*(a*b^5*(b*a)^7*b)^2*b*(b^2*(b*a*b^5*(b*a)^7)^2)^2\
    *b^3*a*b^5*(b*a)^7*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b\
    *a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^3)^2*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*\
    a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^2*b^-1",
    "b^5*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^\
    -6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2*a^-1*b^4*(a^-1*b^-1)^7*b^\
    -5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*\
    (b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2*((a^-1*b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^\
    -1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3\
    *b^-4*a^-1*(a^-1*b^-1)^2)^3*a^-1*((a^-1*b^-1)^7*b^-5*a^-1*b^-2*(b^-1*a^-1)^7*b^-6*a^-1*b\
    ^-1)^2*(a^-1*b^-1)^7*b^-5*a^-1*b^-4*((b^-1*a^-1)^7*b^-6*a^-1)^2*a^-1*b^-2*(a^-1*b^-1*a^-\
    1)^2*b^-7*a^-3*b^-1*a^-1)^2*a^-1*b^-1*(b^-1*a^-1)^7*b^-6*a^-1*b^-2*(b^-2*((b^-1*a^-1)^7*\
    b^-6*a^-1)^2)^2*((b^-1*a^-1)^7*b^-6*a^-1)^3*a^-2*b^-1*(b^-1*a^-1)^2*(a^-1*b^-3)^2*(a^-1*\
    b^-1)^4*b^-1*a^-1*b^-2*a^-2*b^-2*(b^-3*a^-1)^2*b^-2*a^-1*b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-\
    11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)\
    ^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2*(a^-1*((a^-1*b^-1)^7*b^-5*a^-1*b^-2*(b^-1*a^-1)^7*b^-6*a\
    ^-1*b^-1)^2*(a^-1*b^-1)^7*b^-5*a^-1*b^-4*((b^-1*a^-1)^7*b^-6*a^-1)^2*a^-1*b^-2*(a^-1*b^-\
    1*a^-1)^2*b^-7*a^-3*b^-1*a^-1)^2*a^-1*b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^-1*b^-1)^7*b\
    ^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*(\
    a^-1*b^-1)^3*b^-2*((b^-1*a^-1)^7*b^-6*a^-1)^2*b^-2*(b^-4*(b^-1*a^-1)^7*b^-6*a^-1)^2*((b^\
    -1*a^-1)^7*b^-6*a^-1)^2*b^-2*(b^-1*a^-1)^7*b^-3*(b^-2*(b^-1*a^-1)^2)^2*b^-3*a^-2*b^-2"),
   (0, "(b*a)^3*b^4*a^2*b*(b^2*a)^2*b^5*(b*a)^7*b^11*a*b^5*(b*a)^7*b^3*a*b^5*(b*a)^7*b^-4*a^2*b*\
    a^3*b^7*(a*b*a)^2*b^2*a*(a*b^5*(b*a)^7*b)^2*b*(b^2*(b*a*b^5*(b*a)^7)^2)^2*b^3*a*b^5*(b*a\
    )^7*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a\
    *b^5*(b*a)^7*b^-4)^6*b^-1",
    "b^2*a^3*(a*b^2)^2*a^3*b*(b*a)^2*(b*a*b^2)^2*b*a*(a*b)^2*b*a^3*b^5*(b*a)^7*b^4*(b^3*a*b^5\
    *(b*a)^7)^3*(b*a*b^5*(b*a)^7)^2*b^-6*a^2*b*a^3*b^7*(a*b*a)^2*b^2*a*(a*b^5*(b*a)^7*b)^2*b\
    *(b^2*(b*a*b^5*(b*a)^7)^2)^2*b^3*a*b^5*(b*a)^7*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a\
    *b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^4*b^-1*(a*b)^2*a^2*b^4*a^3\
    *b^2*a*b*a^-1*(b*a)^2*(b*a*b^2)^2*b*a*(a*b)^2*b*a^3*b^5*(b*a)^7*b^2*(b*a*b^5*(b*a)^7)^3*\
    b^4*(b*a*b^5*(b*a)^7)^5*b^8*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b\
    *a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4*a^2*b*a^3*b^7*(a*b*a)^2*b^2*a*(a*b^5*(b*a)^7*b\
    )^2*b*(b^2*(b*a*b^5*(b*a)^7)^2)^2*b^3*a*b^5*(b*a)^7*(a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^\
    -1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^2*((a*b)^2*a^2*b^4*a^3\
    *(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^6*b^-\
    1"),
   (2, "b^5*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^\
    -6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2*a^-1*b^4*(a^-1*b^-1)^7*b^\
    -5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*\
    (b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2*((a^-1*b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^\
    -1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3\
    *b^-4*a^-1*(a^-1*b^-1)^2)^3*a^-1*((a^-1*b^-1)^7*b^-5*a^-1*b^-2*(b^-1*a^-1)^7*b^-6*a^-1*b\
    ^-1)^2*(a^-1*b^-1)^7*b^-5*a^-1*b^-4*((b^-1*a^-1)^7*b^-6*a^-1)^2*a^-1*b^-2*(a^-1*b^-1*a^-\
    1)^2*b^-7*a^-3*b^-1*a^-1)^2*a^-1*b^-1*(b^-1*a^-1)^7*b^-6*a^-1*b^-2*(b^-2*((b^-1*a^-1)^7*\
    b^-6*a^-1)^2)^2*((b^-1*a^-1)^7*b^-6*a^-1)^3*a^-2*b^-1*(b^-1*a^-1)^2*(a^-1*b^-3)^2*(a^-1*\
    b^-1)^4*b^-1*a^-1*b^-2*a^-2*b^-2*(b^-3*a^-1)^2*b^-1*(b^-1*a^-1*b^4*(a^-1*b^-1)^7*b^-5*a^\
    -1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*(b^-1\
    *a^-1)^2*a^-3*b^-4*a^-2*b^-1*a^-1)^3*b^-1*(a^-1*b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^-1\
    *b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3*b\
    ^-4*a^-1*(a^-1*b^-1)^2*(a^-1*((a^-1*b^-1)^7*b^-5*a^-1*b^-2*(b^-1*a^-1)^7*b^-6*a^-1*b^-1)\
    ^2*(a^-1*b^-1)^7*b^-5*a^-1*b^-4*((b^-1*a^-1)^7*b^-6*a^-1)^2*a^-1*b^-2*(a^-1*b^-1*a^-1)^2\
    *b^-7*a^-3*b^-1*a^-1)^2)^2*a^-1*b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-2*((b^-1*a^-1)^7*b^-6*a^-\
    1)^3*b^-2*(b^-2*(b^-1*a^-1)^7*b^-6*a^-1)^2*b^-4*a^-2*b^-1*(b^-1*a^-1)^2*a^-1*b^-3*a^-1*b\
    ^-2*(b^-1*a^-1)^6*b^-2*(b^-1*a^-2)^2",
    "a*b^5*(b*a^2)^2*a^7*b^5*(b*a)^7*(b^5*a*b)^2*(a*b)^5*a*b^-8*(a^2*b*a^3*b^7*(a*b*a)^2*b^2*\
    a*(a*b^5*(b*a)^7*b)^2*b*(b^2*(b*a*b^5*(b*a)^7)^2)^2*b^3*a*b^5*(b*a)^7)^2*(a*b)^2*a^2*b^4\
    *a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4*a^\
    2*b*a^3*b^7*(a*b*a)^2*b^2*a*(a*b^5*(b*a)^7*b)^2*b*(b^2*(b*a*b^5*(b*a)^7)^2)^2*b^3*a*b^5*\
    (b*a)^7*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^\
    11*a*b^5*(b*a)^7*b^-4)^8*a*(b^2*a*b)^2*b^4*a^2*b^2*a*b*(b*a)^4*(b^3*a)^2*(a*b)^2*b*a^2*(\
    a*b^5*(b*a)^7*b)^2*a*b^5*(b*a)^7*((b*a*b^5*(b*a)^7)^2*b^2)^2*b^3*a*b^5*(b*a)^7*b^2*(a^2*\
    b*a^3*b^7*(a*b*a)^2*b^2*a*(a*b^5*(b*a)^7*b)^2*b*(b^2*(b*a*b^5*(b*a)^7)^2)^2*b^3*a*b^5*(b\
    *a)^7*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11\
    *a*b^5*(b*a)^7*b^-4)^3)^2*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a\
    *b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^2*b^-1"),
   (2, "a*b*a^4*(a*(a*b)^3)^2*(a*b^3)^2*a*(a*b)^2*b*a^2*(b^2*a*b^5*(b*a)^7*b)^2*b^3*(b*a*b^5*(b*\
    a)^7)^3*(b^5*a*b)^2*(a*b)^5*a*b^10*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7\
    *b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4*a^2*b*a^3*b^7*(a*b*a)^2*b^2*a*(a*b^5*(b\
    *a)^7*b)^2*b*(b^2*(b*a*b^5*(b*a)^7)^2)^2*b^3*a*b^5*(b*a)^7)^2*((a*b)^2*a^2*b^4*a^3*(a*b)\
    ^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^8*b^-1*(a*b\
    )^2*a^2*b^4*a^3*b^2*a*b*a^-1*(b*a)^2*(b*a*b^2)^2*b*a*(a*b)^2*b*a^3*b^5*(b*a)^7*b^2*(b*a*\
    b^5*(b*a)^7)^3*b^4*(b*a*b^5*(b*a)^7)^5*b^8*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5\
    *(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4*a^2*b*a^3*b^7*(a*b*a)^2*b^2*a*(\
    a*b^5*(b*a)^7*b)^2*b*(b^2*(b*a*b^5*(b*a)^7)^2)^2*b^3*a*b^5*(b*a)^7*(a*b)^2*a^2*b^4*a^3*(\
    a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^2*((a*b\
    )^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a\
    )^7*b^-4)^6*b^-1",
    "b^5*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^\
    -6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2*a^-1*b^4*(a^-1*b^-1)^7*b^\
    -5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*\
    (b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2*((a^-1*b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^\
    -1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3\
    *b^-4*a^-1*(a^-1*b^-1)^2)^3*a^-1*((a^-1*b^-1)^7*b^-5*a^-1*b^-2*(b^-1*a^-1)^7*b^-6*a^-1*b\
    ^-1)^2*(a^-1*b^-1)^7*b^-5*a^-1*b^-4*((b^-1*a^-1)^7*b^-6*a^-1)^2*a^-1*b^-2*(a^-1*b^-1*a^-\
    1)^2*b^-7*a^-3*b^-1*a^-1)^2*a^-1*b^-1*(b^-1*a^-1)^7*b^-6*a^-1*b^-2*(b^-2*((b^-1*a^-1)^7*\
    b^-6*a^-1)^2)^2*((b^-1*a^-1)^7*b^-6*a^-1)^3*a^-2*b^-1*(b^-1*a^-1)^2*(a^-1*b^-3)^2*(a^-1*\
    b^-1)^4*b^-1*a^-1*b^-2*a^-2*b^-2*(b^-3*a^-1)^2*b^-2*(a^-1*((a^-1*b^-1)^7*b^-5*a^-1*b^-2*\
    (b^-1*a^-1)^7*b^-6*a^-1*b^-1)^2*(a^-1*b^-1)^7*b^-5*a^-1*b^-4*((b^-1*a^-1)^7*b^-6*a^-1)^2\
    *a^-1*b^-2*(a^-1*b^-1*a^-1)^2*b^-7*a^-3*b^-1*a^-1)^3*a^-1*b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^\
    -11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1\
    )^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2*a^-1*((a^-1*b^-1)^7*b^-5*a^-1*b^-2*(b^-1*a^-1)^7*b^-6*a\
    ^-1*b^-1)^2*(a^-1*b^-1)^7*b^-5*a^-1*b^-4*((b^-1*a^-1)^7*b^-6*a^-1)^2*a^-1*b^-2*(a^-1*b^-\
    1*a^-1)^2*b^-7*a^-3*b^-1*a^-2*b^6*(a^-1*b^-1)^5*a^-1*(b^-1*a^-1*b^-5)^2*b^-3*((b^-1*a^-1\
    )^7*b^-6*a^-1)^2*a^-2*b^-1*(b^-1*a^-1)^2*(a^-1*b^-3)^2*(a^-1*b^-1)^2*(a^-1*b^-2*a^-2)^2*\
    a^-1*b^-3*a^-1*b^-2"),
   (0, "b*(b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7\
    *b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2*a^-1)^6*((a^-1*b^-1)^7\
    *b^-5*a^-1*b^-2*(b^-1*a^-1)^7*b^-6*a^-1*b^-1)^2*(a^-1*b^-1)^7*b^-5*a^-1*b^-4*((b^-1*a^-1\
    )^7*b^-6*a^-1)^2*a^-1*b^-2*(a^-1*b^-1*a^-1)^2*b^-7*a^-3*b^-1*a^-2*b^4*(a^-1*b^-1)^7*b^-5\
    *a^-1*b^-2*(b^-1*a^-1)^7*b^-6*a^-1*b^-11*(a^-1*b^-1)^7*b^-3*(b^-2*a^-1)^2*b^-3*a^-2*b^-3\
    *(b^-1*a^-1)^3*b^-1",
    "a*b*a^2*(a^2*b)^2*a^-2*(b^4*(b*a)^8*b)^2*b^4*(b*a)^7*b^4*((b^5*a*b)^2*(a*b)^5*a)^2*b^-2*\
    (a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*\
    (b*a)^7*b^-4*(a^2*b*a^3*b^7*(a*b*a)^2*b^2*a*(a*b^5*(b*a)^7*b)^2*b*(b^2*(b*a*b^5*(b*a)^7)\
    ^2)^2*b^3*a*b^5*(b*a)^7)^2*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*\
    a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^2*b^-1*(a*b)^2*a^2*b^4*a^3*b^2*a*b*a^-1*(b*a)^\
    2*(b*a*b^2)^2*b*a*(a*b)^2*b*a^3*b^5*(b*a)^7*b^2*(b*a*b^5*(b*a)^7)^3*b^4*(b*a*b^5*(b*a)^7\
    )^5*b^8*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^\
    11*a*b^5*(b*a)^7*b^-4*a^2*b*a^3*b^7*(a*b*a)^2*b^2*a*(a*b^5*(b*a)^7*b)^2*b*(b^2*(b*a*b^5*\
    (b*a)^7)^2)^2*b^3*a*b^5*(b*a)^7*(a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4\
    *(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^2*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*\
    a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^6*b^-1"),
   (2, "b*(b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7\
    *b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2*a^-1)^4*b^4*(a^-1*b^-1\
    )^7*b^-5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1\
    *b^-3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2*((a^-1*b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-1\
    1*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^\
    2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2)^2*a^-1*((a^-1*b^-1)^7*b^-5*a^-1*b^-2*(b^-1*a^-1)^7*b^-6*\
    a^-1*b^-1)^2*(a^-1*b^-1)^7*b^-5*a^-1*b^-4*((b^-1*a^-1)^7*b^-6*a^-1)^2*a^-1*b^-2*(a^-1*b^\
    -1*a^-1)^2*b^-7*a^-3*b^-1*a^-1)^2*a^-1*b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^-1*b^-1)^7*\
    b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*\
    (a^-1*b^-1)^3*b^-6*((b^-1*a^-1)^7*b^-6*a^-1)^5*b^-4*((b^-1*a^-1)^7*b^-6*a^-1)^3*b^-2*(b^\
    -1*a^-1)^7*b^-6*a^-3*b^-1*(b^-1*a^-1)^2*(a^-1*b^-3)^2*(a^-1*b^-1)^3*a*b^-1*a^-1*b^-2*a^-\
    3*b^-4*a^-1*(a^-1*b^-1)^2*a^-1*b*(b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*\
    a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1\
    *b^-1)^2*a^-1)^8*(((a^-1*b^-1)^7*b^-5*a^-1*b^-2*(b^-1*a^-1)^7*b^-6*a^-1*b^-1)^2*(a^-1*b^\
    -1)^7*b^-5*a^-1*b^-4*((b^-1*a^-1)^7*b^-6*a^-1)^2*a^-1*b^-2*(a^-1*b^-1*a^-1)^2*b^-7*a^-3*\
    b^-1*a^-2*b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*\
    a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2*a^-1)^2*b^-10*(\
    a^-1*b^-1)^7*b^-5*a^-1*b^-4*((b^-1*a^-1)^7*b^-6*a^-1)^3*b^-2*(b^-2*(b^-1*a^-1)^7*b^-6*a^\
    -1)^2*b^-2*a^-2*b^-1*(b^-1*a^-1)^2*(a^-1*b^-3)^2*((a^-1*b^-1)^3*a^-1)^2*a^-5*b^-1*a^-1",
    "(a^4*b)^2*a*b*a^4*(a*b^5*(b*a)^7*b)^2*(b^6*a)^2*(b*a)^6*(b^3*a*b^5*(b*a)^7*b^2)^2*b^4*(a\
    ^2*b*a^3*b^7*(a*b*a)^2*b^2*a*(a*b^5*(b*a)^7*b)^2*b*(b^2*(b*a*b^5*(b*a)^7)^2)^2*b^3*a*b^5\
    *(b*a)^7*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b\
    ^11*a*b^5*(b*a)^7*b^-4)^2)^2*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(\
    b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^3*a*(b^2*a*b)^2*b^4*a^2*b^2*a*b*(b*a)^4*(b^3\
    *a)^2*(a*b)^2*b*a^2*(a*b^5*(b*a)^7*b)^2*a*b^5*(b*a)^7*((b*a*b^5*(b*a)^7)^2*b^2)^2*b^3*a*\
    b^5*(b*a)^7*b^2*(a^2*b*a^3*b^7*(a*b*a)^2*b^2*a*(a*b^5*(b*a)^7*b)^2*b*(b^2*(b*a*b^5*(b*a)\
    ^7)^2)^2*b^3*a*b^5*(b*a)^7*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*\
    a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^3)^2*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a\
    *b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^2*b^-1"),
   (2, "(a^2*b)^2*b*(b*a)^6*(b^3*a)^2*(a*b)^2*b*a^2*b*(b^3*a*b^5*(b*a)^7)^2*b^4*(b*a*b^5*(b*a)^7\
    )^3*b^3*(a*b^5*(b*a)^7*b^-4*(a^2*b*a^3*b^7*(a*b*a)^2*b^2*a*(a*b^5*(b*a)^7*b)^2*b*(b^2*(b\
    *a*b^5*(b*a)^7)^2)^2*b^3*a*b^5*(b*a)^7)^2*(a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(\
    b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11)^2*(a*b^5*(b*a)^7*b^-4*(a*b)^2*a^2*b^4*a^3*(a*b)^2*b\
    ^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11)^3*a*b^5*(b*a)^7*b^-4*a*(b^2*a*b)^2\
    *b^4*a^2*b^2*a*b*(b*a)^4*(b^3*a)^2*(a*b)^2*b*a^2*(a*b^5*(b*a)^7*b)^2*a*b^5*(b*a)^7*((b*a\
    *b^5*(b*a)^7)^2*b^2)^2*b^3*a*b^5*(b*a)^7*b^2*(a^2*b*a^3*b^7*(a*b*a)^2*b^2*a*(a*b^5*(b*a)\
    ^7*b)^2*b*(b^2*(b*a*b^5*(b*a)^7)^2)^2*b^3*a*b^5*(b*a)^7*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3\
    *a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^3)^2*((a*b)^2*a^2\
    *b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-\
    4)^2*b^-1",
    "b*(b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7\
    *b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2*a^-1)^4*b^4*(a^-1*b^-1\
    )^7*b^-5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1\
    *b^-3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2*((a^-1*b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-1\
    1*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^\
    2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2)^2*a^-1*((a^-1*b^-1)^7*b^-5*a^-1*b^-2*(b^-1*a^-1)^7*b^-6*\
    a^-1*b^-1)^2*(a^-1*b^-1)^7*b^-5*a^-1*b^-4*((b^-1*a^-1)^7*b^-6*a^-1)^2*a^-1*b^-2*(a^-1*b^\
    -1*a^-1)^2*b^-7*a^-3*b^-1*a^-1)^2*a^-1*b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^-1*b^-1)^7*\
    b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*\
    (a^-1*b^-1)^3*b^-6*((b^-1*a^-1)^7*b^-6*a^-1)^5*b^-4*((b^-1*a^-1)^7*b^-6*a^-1)^3*b^-2*(b^\
    -1*a^-1)^7*b^-6*a^-3*b^-1*(b^-1*a^-1)^2*(a^-1*b^-3)^2*(a^-1*b^-1)^3*a*b^-1*a^-1*b^-2*a^-\
    3*b^-4*a^-1*(a^-1*b^-1)^2*a^-1*b*(b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*\
    a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1\
    *b^-1)^2*a^-1*((a^-1*b^-1)^7*b^-5*a^-1*b^-2*(b^-1*a^-1)^7*b^-6*a^-1*b^-1)^2*(a^-1*b^-1)^\
    7*b^-5*a^-1*b^-4*((b^-1*a^-1)^7*b^-6*a^-1)^2*a^-1*b^-2*(a^-1*b^-1*a^-1)^2*b^-7*a^-3*b^-1\
    *a^-2)^2*((a^-1*b^-1)^7*b^-5*a^-1*b^-2*(b^-1*a^-1)^7*b^-6*a^-1*b^-1)^2*(a^-1*b^-1)^7*b^-\
    5*a^-1*b^-4*((b^-1*a^-1)^7*b^-6*a^-1)^2*a^-1*b^-2*(a^-1*b^-1*a^-1)^2*b^-7*a^-3*b^-1*a^-2\
    *b^-10*((a^-1*b^-1)^7*b^-5*a^-1*b^-3)^2*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*a^-2*b^-1*\
    (b^-1*a^-1)^2*(a^-1*b^-3)^2*(a^-1*b^-1)^2*(a^-1*b^-2*a^-1)^2*a^-1*b^-4*a^-1*b^-1"),
   (2, "b^3*(a*b*a)^2*b*a*b^3*a*(b^2*a*b^5*(b*a)^7*b)^3*b^5*(b^3*a*b^5*(b*a)^7)^2*b^4*((a*b)^2*a\
    ^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b\
    ^-4*a^2*b*a^3*b^7*(a*b*a)^2*b^2*a*(a*b^5*(b*a)^7*b)^2*b*(b^2*(b*a*b^5*(b*a)^7)^2)^2*b^3*\
    a*b^5*(b*a)^7*(a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)\
    ^2*b^11*a*b^5*(b*a)^7*b^-4)^2*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*\
    (b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^6*a*(b^2*a*b)^2*b^4*a^2*b^2*a*b*(b*a)^4*(b^\
    3*a)^2*(a*b)^2*b*a^2*(a*b^5*(b*a)^7*b)^2*a*b^5*(b*a)^7*((b*a*b^5*(b*a)^7)^2*b^2)^2*b^3*a\
    *b^5*(b*a)^7*b^2*(a^2*b*a^3*b^7*(a*b*a)^2*b^2*a*(a*b^5*(b*a)^7*b)^2*b*(b^2*(b*a*b^5*(b*a\
    )^7)^2)^2*b^3*a*b^5*(b*a)^7*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b\
    *a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^3)^2*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*\
    a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^2*b^-1",
    "b*(b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7\
    *b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2*a^-1)^4*b^4*(a^-1*b^-1\
    )^7*b^-5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1\
    *b^-3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2*((a^-1*b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-1\
    1*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^\
    2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2)^2*a^-1*((a^-1*b^-1)^7*b^-5*a^-1*b^-2*(b^-1*a^-1)^7*b^-6*\
    a^-1*b^-1)^2*(a^-1*b^-1)^7*b^-5*a^-1*b^-4*((b^-1*a^-1)^7*b^-6*a^-1)^2*a^-1*b^-2*(a^-1*b^\
    -1*a^-1)^2*b^-7*a^-3*b^-1*a^-1)^2*a^-1*b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^-1*b^-1)^7*\
    b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*\
    (a^-1*b^-1)^3*b^-6*((b^-1*a^-1)^7*b^-6*a^-1)^5*b^-4*((b^-1*a^-1)^7*b^-6*a^-1)^3*b^-2*(b^\
    -1*a^-1)^7*b^-6*a^-3*b^-1*(b^-1*a^-1)^2*(a^-1*b^-3)^2*(a^-1*b^-1)^3*a*b^-1*a^-1*b^-2*a^-\
    3*b^-4*a^-1*(a^-1*b^-1)^2*a^-1*b*(b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*\
    a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1\
    *b^-1)^2*a^-1)^10*((a^-1*b^-1)^7*b^-5*a^-1*b^-2*(b^-1*a^-1)^7*b^-6*a^-1*b^-1)^2*(a^-1*b^\
    -1)^7*b^-5*a^-1*b^-4*((b^-1*a^-1)^7*b^-6*a^-1)^2*a^-1*b^-2*(a^-1*b^-1*a^-1)^2*b^-7*a^-3*\
    b^-1*a^-2*b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*\
    a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2*a^-1*((a^-1*b^-\
    1)^7*b^-5*a^-1*b^-2*(b^-1*a^-1)^7*b^-6*a^-1*b^-1)^2*(a^-1*b^-1)^7*b^-5*a^-1*b^-4*((b^-1*\
    a^-1)^7*b^-6*a^-1)^2*a^-1*b^-2*(a^-1*b^-1*a^-1)^2*b^-7*a^-3*b^-1*a^-2*b^-12*(((a^-1*b^-1\
    )^7*b^-5*a^-1*b^-1)^2*b^-4)^2*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-1*(b^-1*a^-1)^7*b^-5*(\
    b^-1*a^-1)^2*a^-1"),
   (2, "b^5*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^\
    -6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2*a^-1*b^4*(a^-1*b^-1)^7*b^\
    -5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*\
    (b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2*((a^-1*b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^\
    -1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3\
    *b^-4*a^-1*(a^-1*b^-1)^2)^3*a^-1*((a^-1*b^-1)^7*b^-5*a^-1*b^-2*(b^-1*a^-1)^7*b^-6*a^-1*b\
    ^-1)^2*(a^-1*b^-1)^7*b^-5*a^-1*b^-4*((b^-1*a^-1)^7*b^-6*a^-1)^2*a^-1*b^-2*(a^-1*b^-1*a^-\
    1)^2*b^-7*a^-3*b^-1*a^-1)^2*a^-1*b^-1*(b^-1*a^-1)^7*b^-6*a^-1*b^-2*(b^-2*((b^-1*a^-1)^7*\
    b^-6*a^-1)^2)^2*((b^-1*a^-1)^7*b^-6*a^-1)^3*a^-2*b^-1*(b^-1*a^-1)^2*(a^-1*b^-3)^2*(a^-1*\
    b^-1)^4*b^-1*a^-1*b^-2*a^-2*b^-2*(b^-3*a^-1)^2*b^-1*(b^-1*a^-1*b^4*(a^-1*b^-1)^7*b^-5*a^\
    -1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*(b^-1\
    *a^-1)^2*a^-3*b^-4*a^-2*b^-1*a^-1)^5*b^-1*((a^-1*b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^-\
    1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3*\
    b^-4*a^-1*(a^-1*b^-1)^2)^2*a^-1*((a^-1*b^-1)^7*b^-5*a^-1*b^-2*(b^-1*a^-1)^7*b^-6*a^-1*b^\
    -1)^2*(a^-1*b^-1)^7*b^-5*a^-1*b^-4*((b^-1*a^-1)^7*b^-6*a^-1)^2*a^-1*b^-2*(a^-1*b^-1*a^-1\
    )^2*b^-7*a^-3*b^-1*a^-1)^2*a^-1*b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^\
    -1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b\
    ^-1)^3*(b^-2*(b^-1*a^-1)^7*b^-6*a^-1)^2*b^-6*(b^-2*(b^-1*a^-1)^7*b^-6*a^-1)^3*(b^-2*a^-1\
    *b^-1)^2*(a^-1*b^-1*a^-1)^2*b^-3",
    "a*b*a^3*(a*b^2)^2*b^2*a^3*(a*b^5*(b*a)^7*b^5)^2*a*b^5*(b*a)^7*b^11*a*b^5*(b*a)^8*b^5*(b*\
    a)^7*(a^2*b*a^3*b^7*(a*b*a)^2*b^2*a*(a*b^5*(b*a)^7*b)^2*b*(b^2*(b*a*b^5*(b*a)^7)^2)^2*b^\
    3*a*b^5*(b*a)^7*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)\
    ^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^2)^2*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^\
    7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^2*b^-1"),
   (2, "b^5*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^\
    -6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2*a^-1*b^4*(a^-1*b^-1)^7*b^\
    -5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*\
    (b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2*((a^-1*b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^\
    -1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3\
    *b^-4*a^-1*(a^-1*b^-1)^2)^3*a^-1*((a^-1*b^-1)^7*b^-5*a^-1*b^-2*(b^-1*a^-1)^7*b^-6*a^-1*b\
    ^-1)^2*(a^-1*b^-1)^7*b^-5*a^-1*b^-4*((b^-1*a^-1)^7*b^-6*a^-1)^2*a^-1*b^-2*(a^-1*b^-1*a^-\
    1)^2*b^-7*a^-3*b^-1*a^-1)^2*a^-1*b^-1*(b^-1*a^-1)^7*b^-6*a^-1*b^-2*(b^-2*((b^-1*a^-1)^7*\
    b^-6*a^-1)^2)^2*((b^-1*a^-1)^7*b^-6*a^-1)^3*a^-2*b^-1*(b^-1*a^-1)^2*(a^-1*b^-3)^2*(a^-1*\
    b^-1)^4*b^-1*a^-1*b^-2*a^-2*b^-2*(b^-3*a^-1)^2*b^-1*(b^-1*a^-1*b^4*(a^-1*b^-1)^7*b^-5*a^\
    -1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*(b^-1\
    *a^-1)^2*a^-3*b^-4*a^-2*b^-1*a^-1)^2*b^-1*a^-1*((a^-1*b^-1)^7*b^-5*a^-1*b^-2*(b^-1*a^-1)\
    ^7*b^-6*a^-1*b^-1)^2*(a^-1*b^-1)^7*b^-5*a^-1*b^-4*((b^-1*a^-1)^7*b^-6*a^-1)^2*a^-1*b^-2*\
    (a^-1*b^-1*a^-1)^2*b^-7*a^-3*b^-1*a^-2*b^8*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^3*b^-1*(b^-2*(\
    b^-1*a^-1)^7*b^-6*a^-1)^2*b^-2*a^-2*b^-1*(b^-1*a^-1)^2*(a^-1*b^-3)^2*(a^-1*b^-1)^3*b^-1*\
    a^-1*(a^-1*b^-1)^2*a^-2*(a^-1*b^-1)^2*b^-2",
    "b^5*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^\
    -6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2*a^-1*b^4*(a^-1*b^-1)^7*b^\
    -5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*\
    (b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2*((a^-1*b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^\
    -1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3\
    *b^-4*a^-1*(a^-1*b^-1)^2)^3*a^-1*((a^-1*b^-1)^7*b^-5*a^-1*b^-2*(b^-1*a^-1)^7*b^-6*a^-1*b\
    ^-1)^2*(a^-1*b^-1)^7*b^-5*a^-1*b^-4*((b^-1*a^-1)^7*b^-6*a^-1)^2*a^-1*b^-2*(a^-1*b^-1*a^-\
    1)^2*b^-7*a^-3*b^-1*a^-1)^2*a^-1*b^-1*(b^-1*a^-1)^7*b^-6*a^-1*b^-2*(b^-2*((b^-1*a^-1)^7*\
    b^-6*a^-1)^2)^2*((b^-1*a^-1)^7*b^-6*a^-1)^3*a^-2*b^-1*(b^-1*a^-1)^2*(a^-1*b^-3)^2*(a^-1*\
    b^-1)^4*b^-1*a^-1*b^-2*a^-2*b^-2*(b^-3*a^-1)^2*b^-1*(b^-1*a^-1*b^4*(a^-1*b^-1)^7*b^-5*a^\
    -1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*(b^-1\
    *a^-1)^2*a^-3*b^-4*a^-2*b^-1*a^-1)^7*b^-1*a^-1*((a^-1*b^-1)^7*b^-5*a^-1*b^-2*(b^-1*a^-1)\
    ^7*b^-6*a^-1*b^-1)^2*(a^-1*b^-1)^7*b^-5*a^-1*b^-4*((b^-1*a^-1)^7*b^-6*a^-1)^2*a^-1*b^-2*\
    (a^-1*b^-1*a^-1)^2*b^-7*a^-3*b^-1*a^-2*b^-12*(a^-1*b^-1)^7*b^-4*(b^-1*a^-1)^8*b^-6*a^-1*\
    ((b^-1*a^-1)^7*b^-6*a^-1*b^-2)^2*((b^-1*a^-1)^7*b^-6*a^-1)^5*(b^-1*a^-1*b^-1)^2*a^-1*b^-\
    6*a^-1*b^-1"),
   (2, "b*a^3*(a*b)^2*b^2*(b*a)^2*a*(a*b^5*(b*a)^7*b^3)^2*a*b^5*(b*a)^7*b^11*(a*b^5*(b*a)^7*b^3)\
    ^2*b^2*(b*a)^3*a*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a\
    *b^5*(b*a)^7*b^-4*(a^2*b*a^3*b^7*(a*b*a)^2*b^2*a*(a*b^5*(b*a)^7*b)^2*b*(b^2*(b*a*b^5*(b*\
    a)^7)^2)^2*b^3*a*b^5*(b*a)^7)^2*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^\
    4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^8*b^-1",
    "a^5*(b*a^3*b)^2*b^4*(b*a)^7*(b*a*b^5*(b*a)^7*b^4)^2*(b*a*b^5*(b*a)^7)^3*b^8*(a^2*b*a^3*b\
    ^7*(a*b*a)^2*b^2*a*(a*b^5*(b*a)^7*b)^2*b*(b^2*(b*a*b^5*(b*a)^7)^2)^2*b^3*a*b^5*(b*a)^7)^\
    2*(a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^\
    5*(b*a)^7*b^-4*a^2*b*a^3*b^7*(a*b*a)^2*b^2*a*(a*b^5*(b*a)^7*b)^2*b*(b^2*(b*a*b^5*(b*a)^7\
    )^2)^2*b^3*a*b^5*(b*a)^7*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*\
    b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^9*b^-1"),
   (2, "a^3*(a*b^3)^2*b*a^2*(a*b)^5*b^2*a*b^3*a*(a*b)^2*b*a^2*(a*b^5*(b*a)^7*b^3)^3*b*(b*a*b^5*(\
    b*a)^7)^4*b^3*(b*a)^3*a*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2\
    *b^11*a*b^5*(b*a)^7*b^-4*(a^2*b*a^3*b^7*(a*b*a)^2*b^2*a*(a*b^5*(b*a)^7*b)^2*b*(b^2*(b*a*\
    b^5*(b*a)^7)^2)^2*b^3*a*b^5*(b*a)^7)^2*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*\
    a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^9*b^-1",
    "b^4*a*b^2*(a*b^2*a)^2*b*a*(b*a*b^2)^2*b*a*(a*b)^2*b*a^2*b^3*((b*a*b^5*(b*a)^7)^3*b^3*a*b\
    ^5*(b*a)^7)^2*b^12*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b\
    *a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^2*a^2*b*a^3*b^7*(a*b*a)^2*b^2*a*(a*b^5*(b*a)^7*b)^2*b*\
    (b^2*(b*a*b^5*(b*a)^7)^2)^2*b^3*a*b^5*(b*a)^7*(a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b\
    ^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-5"),
   (2, "b^2*(b*a)^2*a*(a*b)^2*a^2*b*(b*a)^2*(b*a*b^2)^2*b*a*(a*b)^2*b*a^2*(b^2*a*b^5*(b*a)^7*b)^\
    2*b^3*(b*a*b^5*(b*a)^7)^3*b^-8*a^2*b*a^3*b^7*(a*b*a)^2*b^2*a*(a*b^5*(b*a)^7*b)^2*b*(b^2*\
    (b*a*b^5*(b*a)^7)^2)^2*b^3*a*b^5*(b*a)^7*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(\
    b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^2*a*(b^2*a*b)^2*b^4*a^2*b^2*a*b*\
    (b*a)^4*(b^3*a)^2*(a*b)^2*b*a^2*(a*b^5*(b*a)^7*b)^2*a*b^5*(b*a)^7*((b*a*b^5*(b*a)^7)^2*b\
    ^2)^2*b^3*a*b^5*(b*a)^7*b^2*(a^2*b*a^3*b^7*(a*b*a)^2*b^2*a*(a*b^5*(b*a)^7*b)^2*b*(b^2*(b\
    *a*b^5*(b*a)^7)^2)^2*b^3*a*b^5*(b*a)^7*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*\
    a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^3)^2*((a*b)^2*a^2*b^4*a^3*(a*b)^2*\
    b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^2*b^-1",
    "a^2*b*a^-4*b^5*(b*a)^7*b^3*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^3*a*b^5*(b*a)^7*b^-6*\
    (a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*\
    (b*a)^7*b^-4*a^2*b*a^3*b^7*(a*b*a)^2*b^2*a*(a*b^5*(b*a)^7*b)^2*b*(b^2*(b*a*b^5*(b*a)^7)^\
    2)^2*b^3*a*b^5*(b*a)^7*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^\
    5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^8*b^-1"),
   (2, "b*(b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7\
    *b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2*a^-1)^9*(((a^-1*b^-1)^\
    7*b^-5*a^-1*b^-2*(b^-1*a^-1)^7*b^-6*a^-1*b^-1)^2*(a^-1*b^-1)^7*b^-5*a^-1*b^-4*((b^-1*a^-\
    1)^7*b^-6*a^-1)^2*a^-1*b^-2*(a^-1*b^-1*a^-1)^2*b^-7*a^-3*b^-1*a^-2)^2*b^4*(a^-1*b^-1)^7*\
    b^-5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-\
    3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^3*b^-2*((b^-1*a^-1)^7*b^-6*a^-1)^4*b^-2*(b^-2\
    *(b^-1*a^-1)^7*b^-6*a^-1)^3*a^-2*b^-1*(b^-1*a^-1)^2*(a^-1*b^-3)^2*(a^-1*b^-1)^4*a^-3*b^-\
    1*(b^-3*a^-1)^2*a^-3",
    "b*(b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7\
    *b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2*a^-1)^2*b^4*(a^-1*b^-1\
    )^7*b^-5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1\
    *b^-3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2*(a^-1*((a^-1*b^-1)^7*b^-5*a^-1*b^-2*(b^\
    -1*a^-1)^7*b^-6*a^-1*b^-1)^2*(a^-1*b^-1)^7*b^-5*a^-1*b^-4*((b^-1*a^-1)^7*b^-6*a^-1)^2*a^\
    -1*b^-2*(a^-1*b^-1*a^-1)^2*b^-7*a^-3*b^-1*a^-1)^3*(a^-1*b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-1\
    1*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^\
    2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2)^2*a^-1*b^-12*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^3*b^-3*(b^-1\
    *a^-1)^7*b^-6*a^-1*b^-2*((b^-1*a^-1)^7*b^-6*a^-1)^5*a^-5*b^-2*(b^-1*a^-1)^2*a^-3*b^-1"),
   (2, "b*(b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7\
    *b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2*a^-1)^8*(((a^-1*b^-1)^\
    7*b^-5*a^-1*b^-2*(b^-1*a^-1)^7*b^-6*a^-1*b^-1)^2*(a^-1*b^-1)^7*b^-5*a^-1*b^-4*((b^-1*a^-\
    1)^7*b^-6*a^-1)^2*a^-1*b^-2*(a^-1*b^-1*a^-1)^2*b^-7*a^-3*b^-1*a^-2)^2*b^4*(a^-1*b^-1)^7*\
    b^-5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-\
    3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^3*b^-2*(b^-2*(b^-1*a^-1)^7*b^-6*a^-1)^2*b^-11\
    *((a^-1*b^-1)^7*b^-5*a^-1*b^-3)^2*(a^-1*b^-1)^7*b^-5*a^-2*(a^-1*b^-1)^2*b^-2*(b^-1*a^-1)\
    ^2*a^-3*b^-1",
    "b*(b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7\
    *b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2*a^-1)^9*(((a^-1*b^-1)^\
    7*b^-5*a^-1*b^-2*(b^-1*a^-1)^7*b^-6*a^-1*b^-1)^2*(a^-1*b^-1)^7*b^-5*a^-1*b^-4*((b^-1*a^-\
    1)^7*b^-6*a^-1)^2*a^-1*b^-2*(a^-1*b^-1*a^-1)^2*b^-7*a^-3*b^-1*a^-2)^2*b^2*(a^-1*b^-1)^7*\
    b^-5*a^-1*b^-2*(b^-4*(b^-1*a^-1)^7*b^-6*a^-1)^2*((b^-1*a^-1)^7*b^-6*a^-1)^2*b^-3*(b^-1*a\
    ^-1)^2*a^-1*(b^-1*a^-2*b^-1)^2*(a^-1*b^-1)^2"),
   (1, "(a*b*a)^2*b*(a^3*b^2*a)^2*b*a*(b*a*b^2)^2*b*a*(a*b)^2*b*a*(a*b^4)^2*b*(b*a)^7*((b^5*a*b)\
    ^2*(a*b)^6*b^3)^2*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*\
    a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^7*b^-1",
    "b*(b^2*a)^2*a*b*a^2*(b^2*a*b^5*(b*a)^7*b)^2*b^3*(b*a*b^5*(b*a)^7)^2*(b*a*b^5*(b*a)^7*b^2\
    )^2*(a^2*b*a^3*b^7*(a*b*a)^2*b^2*a*(a*b^5*(b*a)^7*b)^2*b*(b^2*(b*a*b^5*(b*a)^7)^2)^2*b^3\
    *a*b^5*(b*a)^7)^2*(a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a\
    )^7)^2*b^11*a*b^5*(b*a)^7*b^-4*a^2*b*a^3*b^7*(a*b*a)^2*b^2*a*(a*b^5*(b*a)^7*b)^2*b*(b^2*\
    (b*a*b^5*(b*a)^7)^2)^2*b^3*a*b^5*(b*a)^7*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(\
    b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^10*a*(b^2*a*b)^2*b^4*a^2*b^2*a*b\
    *(b*a)^4*(b^3*a)^2*(a*b)^2*b*a^2*(a*b^5*(b*a)^7*b)^2*a*b^5*(b*a)^7*((b*a*b^5*(b*a)^7)^2*\
    b^2)^2*b^3*a*b^5*(b*a)^7*b^2*(a^2*b*a^3*b^7*(a*b*a)^2*b^2*a*(a*b^5*(b*a)^7*b)^2*b*(b^2*(\
    b*a*b^5*(b*a)^7)^2)^2*b^3*a*b^5*(b*a)^7*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b\
    *a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^3)^2*((a*b)^2*a^2*b^4*a^3*(a*b)^2\
    *b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^2*b^-1"),
   (1, "(b^2*a)^3*a*(a*b)^6*b^2*a*b^3*a*(a*b)^2*b*a^2*b*(b*a*b^5*(b*a)^7)^5*b^4*(b^3*a*b^5*(b*a)\
    ^7)^2*b^-6*(a^2*b*a^3*b^7*(a*b*a)^2*b^2*a*(a*b^5*(b*a)^7*b)^2*b*(b^2*(b*a*b^5*(b*a)^7)^2\
    )^2*b^3*a*b^5*(b*a)^7)^2*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*\
    b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^4*a*(b^2*a*b)^2*b^4*a^2*b^2*a*b*(b*a)^4*(b^3*a)^\
    2*(a*b)^2*b*a^2*(a*b^5*(b*a)^7*b)^2*a*b^5*(b*a)^7*((b*a*b^5*(b*a)^7)^2*b^2)^2*b^3*a*b^5*\
    (b*a)^7*b^2*(a^2*b*a^3*b^7*(a*b*a)^2*b^2*a*(a*b^5*(b*a)^7*b)^2*b*(b^2*(b*a*b^5*(b*a)^7)^\
    2)^2*b^3*a*b^5*(b*a)^7*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^\
    5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^3)^2*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5\
    *(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^2*b^-1",
    "b*(b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7\
    *b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2*a^-1)^10*((a^-1*b^-1)^\
    7*b^-5*a^-1*b^-2*(b^-1*a^-1)^7*b^-6*a^-1*b^-1)^2*(a^-1*b^-1)^7*b^-5*a^-1*b^-4*((b^-1*a^-\
    1)^7*b^-6*a^-1)^2*a^-1*b^-2*(a^-1*b^-1*a^-1)^2*b^-7*a^-3*b^-1*a^-1*(a^-1*b^4*(a^-1*b^-1)\
    ^7*b^-5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*\
    b^-3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2)^2*a^-1*((a^-1*b^-1)^7*b^-5*a^-1*b^-2*(b\
    ^-1*a^-1)^7*b^-6*a^-1*b^-1)^2*(a^-1*b^-1)^7*b^-5*a^-1*b^-4*((b^-1*a^-1)^7*b^-6*a^-1)^2*a\
    ^-1*b^-2*(a^-1*b^-1*a^-1)^2*b^-7*a^-3*b^-1*a^-2*b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^-1\
    *b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3*b\
    ^-4*a^-1*(a^-1*b^-1)^2*a^-1*b^6*(a^-1*b^-1)^7*b^-5*a^-1*b^-2*((b^-1*a^-1)^7*b^-6*a^-1)^2\
    *(((b^-1*a^-1)^7*b^-6*a^-1)^2*b^-4)^2*a^-1*(a^-1*b^-1)^2*b^-1*(b^-1*a^-1)^2*b^-2*a^-1"),
   (2, "b^3*a*b^2*(a^3*b^3*a)^2*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*(b*a*b^5*(b*a)^7*b^2)^2*(b*a\
    *b^5*(b*a)^7)^2*b^4*(a^2*b*a^3*b^7*(a*b*a)^2*b^2*a*(a*b^5*(b*a)^7*b)^2*b*(b^2*(b*a*b^5*(\
    b*a)^7)^2)^2*b^3*a*b^5*(b*a)^7)^2*(a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b\
    ^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4*a^2*b*a^3*b^7*(a*b*a)^2*b^2*a*(a*b^5*(b*a\
    )^7*b)^2*b*(b^2*(b*a*b^5*(b*a)^7)^2)^2*b^3*a*b^5*(b*a)^7*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^\
    3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^10*b^-1*(a*b)^2*\
    a^2*b^4*a^3*b^2*a*b*a^-1*(b*a)^2*(b*a*b^2)^2*b*a*(a*b)^2*b*a^3*b^5*(b*a)^7*b^2*(b*a*b^5*\
    (b*a)^7)^3*b^4*(b*a*b^5*(b*a)^7)^5*b^8*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*\
    a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4*a^2*b*a^3*b^7*(a*b*a)^2*b^2*a*(a*b^\
    5*(b*a)^7*b)^2*b*(b^2*(b*a*b^5*(b*a)^7)^2)^2*b^3*a*b^5*(b*a)^7*(a*b)^2*a^2*b^4*a^3*(a*b)\
    ^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^2*((a*b)^2*\
    a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*\
    b^-4)^6*b^-1",
    "b^5*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^\
    -6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2*a^-1*b^4*(a^-1*b^-1)^7*b^\
    -5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*\
    (b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2*((a^-1*b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^\
    -1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3\
    *b^-4*a^-1*(a^-1*b^-1)^2)^3*a^-1*((a^-1*b^-1)^7*b^-5*a^-1*b^-2*(b^-1*a^-1)^7*b^-6*a^-1*b\
    ^-1)^2*(a^-1*b^-1)^7*b^-5*a^-1*b^-4*((b^-1*a^-1)^7*b^-6*a^-1)^2*a^-1*b^-2*(a^-1*b^-1*a^-\
    1)^2*b^-7*a^-3*b^-1*a^-1)^2*a^-1*b^-1*(b^-1*a^-1)^7*b^-6*a^-1*b^-2*(b^-2*((b^-1*a^-1)^7*\
    b^-6*a^-1)^2)^2*((b^-1*a^-1)^7*b^-6*a^-1)^3*a^-2*b^-1*(b^-1*a^-1)^2*(a^-1*b^-3)^2*(a^-1*\
    b^-1)^4*b^-1*a^-1*b^-2*a^-2*b^-2*(b^-3*a^-1)^2*b^-2*a^-1*b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-\
    11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)\
    ^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2*((a^-1*b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^-1*b^-1)^7*\
    b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*\
    (a^-1*b^-1)^2)^3*a^-1*((a^-1*b^-1)^7*b^-5*a^-1*b^-2*(b^-1*a^-1)^7*b^-6*a^-1*b^-1)^2*(a^-\
    1*b^-1)^7*b^-5*a^-1*b^-4*((b^-1*a^-1)^7*b^-6*a^-1)^2*a^-1*b^-2*(a^-1*b^-1*a^-1)^2*b^-7*a\
    ^-3*b^-1*a^-1)^2*(a^-1*b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^\
    2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2)^2\
    *a^-1*(b^-1*(b^-1*a^-1)^7*b^-6*a^-1*b^-1)^2*b^-5*((b^-1*a^-1)^7*b^-6*a^-1)^2*(b^-6*a^-2*\
    b^-1*a^-1)^2*b^-2"),
   (1, "b*(b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7\
    *b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2*a^-1)^7*(b^-3*(b^-1*a^\
    -1)^6*(b^-1*a^-1*b^-5)^2)^2*(a^-1*b^-1)^7*b^-1*(b^-4*a^-1)^2*a^-1*b^-1*(b^-1*a^-1)^2*(a^\
    -1*b^-3)^2*(a^-1*b^-1)^2*(a^-1*b^-2*a^-3)^2*b^-1*(a^-1*b^-1*a^-1)^2",
    "(a*b)^3*a^2*(b*a^2*b)^2*a*b*(b^3*a*b^5*(b*a)^7)^2*(b*a*b^5*(b*a)^7)^2*b^4*(b^3*a*b^5*(b*\
    a)^7)^2*b^4*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^\
    2*b^11*a*b^5*(b*a)^7*b^-4)^5*b^-1"),
   (2, "b*a*(a*(a*b^2)^2*b)^2*b^2*(b*a)^7*b^8*(b*a*b^5*(b*a)^7)^3*(b^5*a*b)^2*(a*b)^6*(b*a)^3*a*\
    b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4\
    *a^2*b*a^3*b^7*(a*b*a)^2*b^2*a*(a*b^5*(b*a)^7*b)^2*b*(b^2*(b*a*b^5*(b*a)^7)^2)^2*b^3*a*b\
    ^5*(b*a)^7*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2\
    *b^11*a*b^5*(b*a)^7*b^-4)^2*a^2*b*a^3*b^7*(a*b*a)^2*b^2*a*(a*b^5*(b*a)^7*b)^2*b*(b^2*(b*\
    a*b^5*(b*a)^7)^2)^2*b^3*a*b^5*(b*a)^7*b^-1*(a*b)^2*a^2*b^4*a^3*b^2*a*b*a^-1*(b*a)^2*(b*a\
    *b^2)^2*b*a*(a*b)^2*b*a^3*b^5*(b*a)^7*b^2*(b*a*b^5*(b*a)^7)^3*b^4*(b*a*b^5*(b*a)^7)^5*b^\
    8*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b\
    ^5*(b*a)^7*b^-4*a^2*b*a^3*b^7*(a*b*a)^2*b^2*a*(a*b^5*(b*a)^7*b)^2*b*(b^2*(b*a*b^5*(b*a)^\
    7)^2)^2*b^3*a*b^5*(b*a)^7*(a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*\
    b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^2*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*\
    (b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^6*b^-1",
    "b^5*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^\
    -6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2*a^-1*b^4*(a^-1*b^-1)^7*b^\
    -5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*\
    (b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2*((a^-1*b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^\
    -1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3\
    *b^-4*a^-1*(a^-1*b^-1)^2)^3*a^-1*((a^-1*b^-1)^7*b^-5*a^-1*b^-2*(b^-1*a^-1)^7*b^-6*a^-1*b\
    ^-1)^2*(a^-1*b^-1)^7*b^-5*a^-1*b^-4*((b^-1*a^-1)^7*b^-6*a^-1)^2*a^-1*b^-2*(a^-1*b^-1*a^-\
    1)^2*b^-7*a^-3*b^-1*a^-1)^2*a^-1*b^-1*(b^-1*a^-1)^7*b^-6*a^-1*b^-2*(b^-2*((b^-1*a^-1)^7*\
    b^-6*a^-1)^2)^2*((b^-1*a^-1)^7*b^-6*a^-1)^3*a^-2*b^-1*(b^-1*a^-1)^2*(a^-1*b^-3)^2*(a^-1*\
    b^-1)^4*b^-1*a^-1*b^-2*a^-2*b^-2*(b^-3*a^-1)^2*b^-2*(a^-1*((a^-1*b^-1)^7*b^-5*a^-1*b^-2*\
    (b^-1*a^-1)^7*b^-6*a^-1*b^-1)^2*(a^-1*b^-1)^7*b^-5*a^-1*b^-4*((b^-1*a^-1)^7*b^-6*a^-1)^2\
    *a^-1*b^-2*(a^-1*b^-1*a^-1)^2*b^-7*a^-3*b^-1*a^-1)^2*(a^-1*b^4*(a^-1*b^-1)^7*b^-5*a^-1*b\
    ^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-\
    1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2)^3*a^-1*b^6*(a^-1*b^-1)^7*b^-5*a^-1*(b^-2*(b^-1*a^-1)^\
    7*b^-6*a^-1*b^-2)^2*b^-4*(b^-1*a^-1)^7*b^-6*a^-3*b^-1*(b^-1*a^-1)^2*(a^-1*b^-3)^2*(a^-1*\
    b^-1)^3*b^-1*a^-3*b^-1*(b^-1*a^-1)^2*b^-3*a^-3"),
   (1, "b*(b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7\
    *b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2*a^-1)^2*b^4*(a^-1*b^-1\
    )^7*b^-5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1\
    *b^-3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2*(a^-1*((a^-1*b^-1)^7*b^-5*a^-1*b^-2*(b^\
    -1*a^-1)^7*b^-6*a^-1*b^-1)^2*(a^-1*b^-1)^7*b^-5*a^-1*b^-4*((b^-1*a^-1)^7*b^-6*a^-1)^2*a^\
    -1*b^-2*(a^-1*b^-1*a^-1)^2*b^-7*a^-3*b^-1*a^-1)^3*(a^-1*b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-1\
    1*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^\
    2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2)^3*a^-1*(b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b^-1)^2*b^-5*((b^-1\
    *a^-1)^7*b^-6*a^-1)^2*b^-4*(b^-1*a^-1)^7*b^-6*a^-3*b^-1*(b^-1*a^-1)^2*a^-1*b^-3*a^-1*b^-\
    2*(b^-1*a^-1)^6*a^-2*(b^-1*a^-1*b^-2)^2",
    "b*(b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7\
    *b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2*a^-1)^9*(((a^-1*b^-1)^\
    7*b^-5*a^-1*b^-2*(b^-1*a^-1)^7*b^-6*a^-1*b^-1)^2*(a^-1*b^-1)^7*b^-5*a^-1*b^-4*((b^-1*a^-\
    1)^7*b^-6*a^-1)^2*a^-1*b^-2*(a^-1*b^-1*a^-1)^2*b^-7*a^-3*b^-1*a^-2)^2*(b^-1*(b^-1*a^-1)^\
    7*b^-6*a^-1*b^-1)^2*(a^-1*b^-1)^5*a^-1*(b^-1*a^-1*b^-5)^2*(a^-1*b^-1)^7*b^-3*(b^-2*a^-1)\
    ^2*a^-1*(b^-1*a^-1*b^-2)^2*a^-1*b^-2*a^-2"),
   (2, "a^4*b^2*a*(a^2*b)^2*a^3*b*(b*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2)^2*(b^-2*(a*b)^2*a^2*\
    b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-2\
    )^2*b^-2*(a^2*b*a^3*b^7*(a*b*a)^2*b^2*a*(a*b^5*(b*a)^7*b)^2*b*(b^2*(b*a*b^5*(b*a)^7)^2)^\
    2*b^3*a*b^5*(b*a)^7)^2*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^\
    5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^2*b^-1*(a*b)^2*a^2*b^4*a^3*b^2*a*b*a^-1*(b*a)^2*(b\
    *a*b^2)^2*b*a*(a*b)^2*b*a^3*b^5*(b*a)^7*b^2*(b*a*b^5*(b*a)^7)^3*b^4*(b*a*b^5*(b*a)^7)^5*\
    b^8*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a\
    *b^5*(b*a)^7*b^-4*a^2*b*a^3*b^7*(a*b*a)^2*b^2*a*(a*b^5*(b*a)^7*b)^2*b*(b^2*(b*a*b^5*(b*a\
    )^7)^2)^2*b^3*a*b^5*(b*a)^7*(a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*\
    a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^2*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^\
    5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^6*b^-1",
    "(a*b)^2*b^4*a^2*(a*b)^6*b^2*a*b^3*a*(a*b)^2*b*a*(a*b^4)^2*b*(b*a)^7*(b*a*b^5*(b*a)^7*b^2\
    )^2*(b*a*b^5*(b*a)^7)^2*b^4*(b*a*b^5*(b*a)^7)^2*b^12*a^2*b*a^3*b^7*(a*b*a)^2*b^2*a*(a*b^\
    5*(b*a)^7*b)^2*b*(b^2*(b*a*b^5*(b*a)^7)^2)^2*b^3*a*b^5*(b*a)^7*((a*b)^2*a^2*b^4*a^3*(a*b\
    )^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^2*(a^2*b*a\
    ^3*b^7*(a*b*a)^2*b^2*a*(a*b^5*(b*a)^7*b)^2*b*(b^2*(b*a*b^5*(b*a)^7)^2)^2*b^3*a*b^5*(b*a)\
    ^7)^2*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11\
    *a*b^5*(b*a)^7*b^-4)^2*b^-1*(a*b)^2*a^2*b^4*a^3*b^2*a*b*a^-1*(b*a)^2*(b*a*b^2)^2*b*a*(a*\
    b)^2*b*a^3*b^5*(b*a)^7*b^2*(b*a*b^5*(b*a)^7)^3*b^4*(b*a*b^5*(b*a)^7)^5*b^8*((a*b)^2*a^2*\
    b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4\
    *a^2*b*a^3*b^7*(a*b*a)^2*b^2*a*(a*b^5*(b*a)^7*b)^2*b*(b^2*(b*a*b^5*(b*a)^7)^2)^2*b^3*a*b\
    ^5*(b*a)^7*(a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*\
    b^11*a*b^5*(b*a)^7*b^-4)^2*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*\
    a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^6*b^-1"),
   (1, "b*(b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7\
    *b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2*a^-1)^2*b^4*(a^-1*b^-1\
    )^7*b^-5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1\
    *b^-3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2*(a^-1*((a^-1*b^-1)^7*b^-5*a^-1*b^-2*(b^\
    -1*a^-1)^7*b^-6*a^-1*b^-1)^2*(a^-1*b^-1)^7*b^-5*a^-1*b^-4*((b^-1*a^-1)^7*b^-6*a^-1)^2*a^\
    -1*b^-2*(a^-1*b^-1*a^-1)^2*b^-7*a^-3*b^-1*a^-1)^4*a^-1*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^4*\
    (b^-1*(b^-1*a^-1)^7*b^-6*a^-1*b^-1)^2*b^-5*a^-2*b^-1*(b^-1*a^-1)^2*(a^-1*b^-3)^2*(a^-1*b\
    ^-1)^3*a^-2*(a^-1*b^-2)^2*b^-1*a^-3*b^-1",
    "b*(b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7\
    *b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2*a^-1)^4*b^4*(a^-1*b^-1\
    )^7*b^-5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1\
    *b^-3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2*((a^-1*b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-1\
    1*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^\
    2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2)^2*a^-1*((a^-1*b^-1)^7*b^-5*a^-1*b^-2*(b^-1*a^-1)^7*b^-6*\
    a^-1*b^-1)^2*(a^-1*b^-1)^7*b^-5*a^-1*b^-4*((b^-1*a^-1)^7*b^-6*a^-1)^2*a^-1*b^-2*(a^-1*b^\
    -1*a^-1)^2*b^-7*a^-3*b^-1*a^-1)^2*a^-1*b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^-1*b^-1)^7*\
    b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*\
    (a^-1*b^-1)^3*b^-6*((b^-1*a^-1)^7*b^-6*a^-1)^5*b^-4*((b^-1*a^-1)^7*b^-6*a^-1)^3*b^-2*(b^\
    -1*a^-1)^7*b^-6*a^-3*b^-1*(b^-1*a^-1)^2*(a^-1*b^-3)^2*(a^-1*b^-1)^3*a*b^-1*a^-1*b^-2*a^-\
    3*b^-4*a^-1*(a^-1*b^-1)^2*a^-1*b*(b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*\
    a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1\
    *b^-1)^2*a^-1)^5*((a^-1*b^-1)^7*b^-5*a^-1*b^-2*(b^-1*a^-1)^7*b^-6*a^-1*b^-1)^2*(a^-1*b^-\
    1)^7*b^-5*a^-1*b^-4*((b^-1*a^-1)^7*b^-6*a^-1)^2*a^-1*b^-2*(a^-1*b^-1*a^-1)^2*b^-7*a^-3*b\
    ^-1*a^-1*(a^-1*b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(\
    b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2)^2*a^-1*b^\
    -12*(a^-1*b^-1)^7*b^-5*a^-1*b^-2*(b^-1*a^-1)^7*b^-6*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*\
    b^-1)^2*(a^-1*b^-1)^7*b^-5*a^-3*b^-1*(b^-1*a^-1)^2*(a^-1*b^-3)^2*a^-1*b^-1*((a^-1*b^-1)^\
    2*b^-1*a^-2)^2*(b^-1*a^-1)^2*b^-2"),
   (1, "(a^3*b*a)^2*b^2*a^2*(a*b)^4*b^2*a*b^3*a*(a*b)^2*b*a^2*(a*b^5*(b*a)^7*b)^2*b*(b*a*b^5*(b*\
    a)^7)^3*b^-2*(b^-4*(a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*\
    a)^7)^2*b^11*a*b^5*(b*a)^7)^2*b^-4*a^2*b*a^3*b^7*(a*b*a)^2*b^2*a*(a*b^5*(b*a)^7*b)^2*b*(\
    b^2*(b*a*b^5*(b*a)^7)^2)^2*b^3*a*b^5*(b*a)^7*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b\
    ^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^2*b^-1*(a*b)^2*a^2*b^4*a^3*b\
    ^2*a*b*a^-1*(b*a)^2*(b*a*b^2)^2*b*a*(a*b)^2*b*a^3*b^5*(b*a)^7*b^2*(b*a*b^5*(b*a)^7)^3*b^\
    4*(b*a*b^5*(b*a)^7)^5*b^8*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a\
    *b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4*a^2*b*a^3*b^7*(a*b*a)^2*b^2*a*(a*b^5*(b*a)^7*b)^\
    2*b*(b^2*(b*a*b^5*(b*a)^7)^2)^2*b^3*a*b^5*(b*a)^7*(a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1\
    *a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^2*((a*b)^2*a^2*b^4*a^3*(\
    a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^6*b^-1",
    "b^3*a*(a^2*b^2)^2*a*b*a^3*b^5*(b*a)^7*(b*a*b^5*(b*a)^7*b^4)^2*b^2*(b^3*a*b^5*(b*a)^7)^2*\
    b^4*(a^2*b*a^3*b^7*(a*b*a)^2*b^2*a*(a*b^5*(b*a)^7*b)^2*b*(b^2*(b*a*b^5*(b*a)^7)^2)^2*b^3\
    *a*b^5*(b*a)^7*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^\
    7)^2*b^11*a*b^5*(b*a)^7*b^-4)^2)^2*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7\
    *b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^2*b^-1"),
   (1, "b^2*(b*a^2*b*a)^2*b^2*(b*a)^2*a*b^5*(b*a)^7*b^2*(b*a*b^5*(b*a)^6*(b*a*b^6)^2*(a*b)^6*a)^\
    2*((a^2*b*a^3*b^7*(a*b*a)^2*b^2*a*(a*b^5*(b*a)^7*b)^2*b*(b^2*(b*a*b^5*(b*a)^7)^2)^2*b^3*\
    a*b^5*(b*a)^7)^2*(a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)\
    ^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^2*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b\
    ^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^3*b^-1",
    "b*(b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7\
    *b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2*a^-1)^2*((a^-1*b^-1)^7\
    *b^-5*a^-1*b^-2*(b^-1*a^-1)^7*b^-6*a^-1*b^-1)^2*(a^-1*b^-1)^7*b^-5*a^-1*b^-4*((b^-1*a^-1\
    )^7*b^-6*a^-1)^2*a^-1*b^-2*(a^-1*b^-1*a^-1)^2*b^-7*a^-3*b^-1*a^-1*(a^-1*b^4*(a^-1*b^-1)^\
    7*b^-5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b\
    ^-3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2)^2*a^-1*b^-3*((b^-1*a^-1)^7*b^-6*a^-1)^2*\
    (((b^-1*a^-1)^7*b^-6*a^-1)^2*b^-2)^2*b^-2*(b^-1*a^-1)^7*b^-6*a^-3*b^-1*(b^-1*a^-1)^2*(a^\
    -1*b^-3)^2*(a^-1*b^-1)^4*(b^-1*a^-1*b^-1)^2*a^-1*b^-1*a^-2*b^-1"),
   (1, "(a*b)^2*b^4*(b*a^3)^2*b*(b^3*a*b^5*(b*a)^7)^2*(b*a*b^5*(b*a)^7*b^4)^2*b*a*b^5*(b*a)^7*b^\
    12*a^2*b*a^3*b^7*(a*b*a)^2*b^2*a*(a*b^5*(b*a)^7*b)^2*b*(b^2*(b*a*b^5*(b*a)^7)^2)^2*b^3*a\
    *b^5*(b*a)^7*(a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^\
    2*b^11*a*b^5*(b*a)^7*b^-4*(a^2*b*a^3*b^7*(a*b*a)^2*b^2*a*(a*b^5*(b*a)^7*b)^2*b*(b^2*(b*a\
    *b^5*(b*a)^7)^2)^2*b^3*a*b^5*(b*a)^7)^2*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b\
    *a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^4*a*(b^2*a*b)^2*b^4*a^2*b^2*a*b*(\
    b*a)^4*(b^3*a)^2*(a*b)^2*b*a^2*(a*b^5*(b*a)^7*b)^2*a*b^5*(b*a)^7*((b*a*b^5*(b*a)^7)^2*b^\
    2)^2*b^3*a*b^5*(b*a)^7*b^2*(a^2*b*a^3*b^7*(a*b*a)^2*b^2*a*(a*b^5*(b*a)^7*b)^2*b*(b^2*(b*\
    a*b^5*(b*a)^7)^2)^2*b^3*a*b^5*(b*a)^7*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a\
    )^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^3)^2*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b\
    ^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^2*b^-1",
    "a*(a*b)^3*a^2*b^5*(b*a)^4*(b^3*a)^2*(a*b)^2*b*a^2*b^3*(b*a*b^5*(b*a)^7)^2*b^4*((b^5*a*b)\
    ^2*(a*b)^5*a)^2*b*a*b^5*(b*a)^7*b^12*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)\
    ^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^5*b^-1"),
   (2, "b^5*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^\
    -6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2*a^-1*b^4*(a^-1*b^-1)^7*b^\
    -5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*\
    (b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2*((a^-1*b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^\
    -1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3\
    *b^-4*a^-1*(a^-1*b^-1)^2)^3*a^-1*((a^-1*b^-1)^7*b^-5*a^-1*b^-2*(b^-1*a^-1)^7*b^-6*a^-1*b\
    ^-1)^2*(a^-1*b^-1)^7*b^-5*a^-1*b^-4*((b^-1*a^-1)^7*b^-6*a^-1)^2*a^-1*b^-2*(a^-1*b^-1*a^-\
    1)^2*b^-7*a^-3*b^-1*a^-1)^2*a^-1*b^-1*(b^-1*a^-1)^7*b^-6*a^-1*b^-2*(b^-2*((b^-1*a^-1)^7*\
    b^-6*a^-1)^2)^2*((b^-1*a^-1)^7*b^-6*a^-1)^3*a^-2*b^-1*(b^-1*a^-1)^2*(a^-1*b^-3)^2*(a^-1*\
    b^-1)^4*b^-1*a^-1*b^-2*a^-2*b^-2*(b^-3*a^-1)^2*b^-1*(b^-1*a^-1*((a^-1*b^-1)^7*b^-5*a^-1*\
    b^-2*(b^-1*a^-1)^7*b^-6*a^-1*b^-1)^2*(a^-1*b^-1)^7*b^-5*a^-1*b^-4*((b^-1*a^-1)^7*b^-6*a^\
    -1)^2*a^-1*b^-2*(a^-1*b^-1*a^-1)^2*b^-7*a^-3*b^-1*a^-2*b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-11\
    *((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2\
    *a^-3*b^-4*a^-2*b^-1*a^-1)^2*b^-1*a^-1*b^8*(a^-1*b^-1)^7*b^-5*a^-1*(b^-4*(b^-1*a^-1)^7*b\
    ^-6*a^-1*b^-4)^2*b^-1*a^-4*b^-6*a^-4",
    "(a*b^2*a)^2*(a*(a*b)^2)^2*a*(b*a*b^2)^2*b*a^2*b*(a*b^2*a)^2*b^5*(b*a)^7*b^11*(a*b^5*(b*a\
    )^7*b)^3*a*b^5*(b*a)^7*b^10*(a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*\
    a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4*a^2*b*a^3*b^7*(a*b*a)^2*b^2*a*(a*b^5*(b*a)^7*b)\
    ^2*b*(b^2*(b*a*b^5*(b*a)^7)^2)^2*b^3*a*b^5*(b*a)^7*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^\
    -1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^9*a*(b^2*a*b)^2*b^4*a^\
    2*b^2*a*b*(b*a)^4*(b^3*a)^2*(a*b)^2*b*a^2*(a*b^5*(b*a)^7*b)^2*a*b^5*(b*a)^7*((b*a*b^5*(b\
    *a)^7)^2*b^2)^2*b^3*a*b^5*(b*a)^7*b^2*(a^2*b*a^3*b^7*(a*b*a)^2*b^2*a*(a*b^5*(b*a)^7*b)^2\
    *b*(b^2*(b*a*b^5*(b*a)^7)^2)^2*b^3*a*b^5*(b*a)^7*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1\
    *a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^3)^2*((a*b)^2*a^2*b^4*a^\
    3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^2*b^\
    -1"),
   (2, "a*b*(a*b*a)^2*(b^3*a*b^4)^2*b*(b*a)^7*b^2*(b*a*b^5*(b*a)^7*b^3*a*b^5*(b*a)^7)^2*b*a*b^5*\
    (b*a)^7*b^4*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^\
    2*b^11*a*b^5*(b*a)^7*b^-4)^2*(a^2*b*a^3*b^7*(a*b*a)^2*b^2*a*(a*b^5*(b*a)^7*b)^2*b*(b^2*(\
    b*a*b^5*(b*a)^7)^2)^2*b^3*a*b^5*(b*a)^7)^2*b^-1*(a*b)^2*a^2*b^4*a^3*b^2*a*b*a^-1*(b*a)^2\
    *(b*a*b^2)^2*b*a*(a*b)^2*b*a^3*b^5*(b*a)^7*b^2*(b*a*b^5*(b*a)^7)^3*b^4*(b*a*b^5*(b*a)^7)\
    ^5*b^8*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^1\
    1*a*b^5*(b*a)^7*b^-4*a^2*b*a^3*b^7*(a*b*a)^2*b^2*a*(a*b^5*(b*a)^7*b)^2*b*(b^2*(b*a*b^5*(\
    b*a)^7)^2)^2*b^3*a*b^5*(b*a)^7*(a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*\
    (b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^2*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a\
    *b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^6*a*(b^2*a*b)^2*b^4*a^2*b^\
    2*a*b*(b*a)^4*(b^3*a)^2*(a*b)^2*b*a^2*(a*b^5*(b*a)^7*b)^2*a*b^5*(b*a)^7*((b*a*b^5*(b*a)^\
    7)^2*b^2)^2*b^3*a*b^5*(b*a)^7*b^2*(a^2*b*a^3*b^7*(a*b*a)^2*b^2*a*(a*b^5*(b*a)^7*b)^2*b*(\
    b^2*(b*a*b^5*(b*a)^7)^2)^2*b^3*a*b^5*(b*a)^7*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b\
    ^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^3)^2*((a*b)^2*a^2*b^4*a^3*(a\
    *b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^2*b^-1",
    "b*(b*a)^2*b^4*a^2*b*a*(b*a*b^2)^2*b*a*(a*b)^2*b*a^3*b^5*(b*a)^8*b^5*(b*a)^7*((b*a*b^5*(b\
    *a)^7)^2*b^2)^2*b*a*b^5*(b*a)^7*a^2*b*a^3*b^7*(a*b*a)^2*b^2*a*(a*b^5*(b*a)^7*b)^2*b*(b^2\
    *(b*a*b^5*(b*a)^7)^2)^2*b^3*a*b^5*(b*a)^7*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*\
    (b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^7*b^-1"),
   (1, "(b*a)^2*a*b^3*(b*a^2)^2*a*(b^2*a*b^5*(b*a)^7*b)^2*b^7*(b*a*b^5*(b*a)^7)^3*b^5*(b*a^2)^2*\
    a*b^7*(a*b*a)^2*b^2*a*(a*b^5*(b*a)^7*b)^2*b*(b^2*(b*a*b^5*(b*a)^7)^2)^2*b^3*a*b^5*(b*a)^\
    7*(a^2*b*a^3*b^7*(a*b*a)^2*b^2*a*(a*b^5*(b*a)^7*b)^2*b*(b^2*(b*a*b^5*(b*a)^7)^2)^2*b^3*a\
    *b^5*(b*a)^7*(a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^\
    2*b^11*a*b^5*(b*a)^7*b^-4)^2*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(\
    b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^4*b^-1*(a*b)^2*a^2*b^4*a^3*b^2*a*b*a^-1*(b*a\
    )^2*(b*a*b^2)^2*b*a*(a*b)^2*b*a^3*b^5*(b*a)^7*b^2*(b*a*b^5*(b*a)^7)^3*b^4*(b*a*b^5*(b*a)\
    ^7)^5*b^8*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*\
    b^11*a*b^5*(b*a)^7*b^-4*a^2*b*a^3*b^7*(a*b*a)^2*b^2*a*(a*b^5*(b*a)^7*b)^2*b*(b^2*(b*a*b^\
    5*(b*a)^7)^2)^2*b^3*a*b^5*(b*a)^7*(a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b\
    ^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^2*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-\
    1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^6*b^-1",
    "b*(b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7\
    *b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2*a^-1)^4*((a^-1*b^-1)^7\
    *b^-5*a^-1*b^-2*(b^-1*a^-1)^7*b^-6*a^-1*b^-1)^2*(a^-1*b^-1)^7*b^-5*a^-1*b^-4*((b^-1*a^-1\
    )^7*b^-6*a^-1)^2*a^-1*b^-2*(a^-1*b^-1*a^-1)^2*b^-7*a^-1*(a^-2*b^-1)^2*b^-4*(b^-2*((b^-1*\
    a^-1)^7*b^-6*a^-1)^2)^2*(b^-2*(b^-1*a^-1)^7*b^-6*a^-1)^2*((b^-1*a^-1)^7*b^-6*a^-1)^2*b^-\
    2*a^-2*b^-1*(b^-1*a^-1)^2*(a^-1*b^-3)^2*(a^-1*b^-1)^3*a^-2*(a^-1*b^-2)^2*b^-4*a^-1"),
   (1, "b^5*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^\
    -6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2*a^-1*b^4*(a^-1*b^-1)^7*b^\
    -5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*\
    (b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2*((a^-1*b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^\
    -1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3\
    *b^-4*a^-1*(a^-1*b^-1)^2)^3*a^-1*((a^-1*b^-1)^7*b^-5*a^-1*b^-2*(b^-1*a^-1)^7*b^-6*a^-1*b\
    ^-1)^2*(a^-1*b^-1)^7*b^-5*a^-1*b^-4*((b^-1*a^-1)^7*b^-6*a^-1)^2*a^-1*b^-2*(a^-1*b^-1*a^-\
    1)^2*b^-7*a^-3*b^-1*a^-1)^2*a^-1*b^-1*(b^-1*a^-1)^7*b^-6*a^-1*b^-2*(b^-2*((b^-1*a^-1)^7*\
    b^-6*a^-1)^2)^2*((b^-1*a^-1)^7*b^-6*a^-1)^3*a^-2*b^-1*(b^-1*a^-1)^2*(a^-1*b^-3)^2*(a^-1*\
    b^-1)^4*b^-1*a^-1*b^-2*a^-2*b^-2*(b^-3*a^-1)^2*b^-2*(a^-1*((a^-1*b^-1)^7*b^-5*a^-1*b^-2*\
    (b^-1*a^-1)^7*b^-6*a^-1*b^-1)^2*(a^-1*b^-1)^7*b^-5*a^-1*b^-4*((b^-1*a^-1)^7*b^-6*a^-1)^2\
    *a^-1*b^-2*(a^-1*b^-1*a^-1)^2*b^-7*a^-3*b^-1*a^-1)^2*a^-1*b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^\
    -11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1\
    )^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2*a^-1*b^4*(((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-2)^2*b^-5\
    *((b^-1*a^-1)^7*b^-6*a^-1)^3*a^-1*b^-3*a^-3*(a^-3*b^-1)^2",
    "a^2*b*a*b^-1*a*(a*b^5*(b*a)^7*b^3*a*b^5*(b*a)^7*b)^2*a*b^5*(b*a)^7*(b*a*b^5*(b*a)^7*b^4)\
    ^2*b^4*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^1\
    1*a*b^5*(b*a)^7*b^-4)^2*a^2*b*a^3*b^7*(a*b*a)^2*b^2*a*(a*b^5*(b*a)^7*b)^2*b*(b^2*(b*a*b^\
    5*(b*a)^7)^2)^2*b^3*a*b^5*(b*a)^7*(a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b\
    ^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-5"),
   (2, "b*(b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7\
    *b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2*a^-1)^4*b^4*(a^-1*b^-1\
    )^7*b^-5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1\
    *b^-3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2*((a^-1*b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-1\
    1*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^\
    2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2)^2*a^-1*((a^-1*b^-1)^7*b^-5*a^-1*b^-2*(b^-1*a^-1)^7*b^-6*\
    a^-1*b^-1)^2*(a^-1*b^-1)^7*b^-5*a^-1*b^-4*((b^-1*a^-1)^7*b^-6*a^-1)^2*a^-1*b^-2*(a^-1*b^\
    -1*a^-1)^2*b^-7*a^-3*b^-1*a^-1)^2*a^-1*b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^-1*b^-1)^7*\
    b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*\
    (a^-1*b^-1)^3*b^-6*((b^-1*a^-1)^7*b^-6*a^-1)^5*b^-4*((b^-1*a^-1)^7*b^-6*a^-1)^3*b^-2*(b^\
    -1*a^-1)^7*b^-6*a^-3*b^-1*(b^-1*a^-1)^2*(a^-1*b^-3)^2*(a^-1*b^-1)^3*a*b^-1*a^-1*b^-2*a^-\
    3*b^-4*a^-1*(a^-1*b^-1)^2*a^-1*b^5*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-\
    1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^\
    -1)^2*a^-1*b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1\
    *a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2*(a^-1*((a^-1*b\
    ^-1)^7*b^-5*a^-1*b^-2*(b^-1*a^-1)^7*b^-6*a^-1*b^-1)^2*(a^-1*b^-1)^7*b^-5*a^-1*b^-4*((b^-\
    1*a^-1)^7*b^-6*a^-1)^2*a^-1*b^-2*(a^-1*b^-1*a^-1)^2*b^-7*a^-3*b^-1*a^-1)^2*(a^-1*b^4*(a^\
    -1*b^-1)^7*b^-5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1\
    *b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2)^2*a^-1*b^2*(((a^-1*b^-1)^7*b^-5\
    *a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b^-1)^2*b^-1*a^-1*(a^-2*b^-1)^2*a^-3*b^-2*a^-\
    4",
    "b*(b*a*b^2*a)^2*(a*b)^2*b^4*((b*a*b^5*(b*a)^7)^2*b^3*a*b^5*(b*a)^7)^2*(b*a*b^5*(b*a)^7)^\
    2*b^2*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11\
    *a*b^5*(b*a)^7*b^-4)^10*a*(b^2*a*b)^2*b^4*a^2*b^2*a*b*(b*a)^4*(b^3*a)^2*(a*b)^2*b*a^2*(a\
    *b^5*(b*a)^7*b)^2*a*b^5*(b*a)^7*((b*a*b^5*(b*a)^7)^2*b^2)^2*b^3*a*b^5*(b*a)^7*b^2*(a^2*b\
    *a^3*b^7*(a*b*a)^2*b^2*a*(a*b^5*(b*a)^7*b)^2*b*(b^2*(b*a*b^5*(b*a)^7)^2)^2*b^3*a*b^5*(b*\
    a)^7*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*\
    a*b^5*(b*a)^7*b^-4)^3)^2*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*\
    b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^2*b^-1"),
   (1, "b^5*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^\
    -6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2*a^-1*b^4*(a^-1*b^-1)^7*b^\
    -5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*\
    (b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2*((a^-1*b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^\
    -1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3\
    *b^-4*a^-1*(a^-1*b^-1)^2)^3*a^-1*((a^-1*b^-1)^7*b^-5*a^-1*b^-2*(b^-1*a^-1)^7*b^-6*a^-1*b\
    ^-1)^2*(a^-1*b^-1)^7*b^-5*a^-1*b^-4*((b^-1*a^-1)^7*b^-6*a^-1)^2*a^-1*b^-2*(a^-1*b^-1*a^-\
    1)^2*b^-7*a^-3*b^-1*a^-1)^2*a^-1*b^-1*(b^-1*a^-1)^7*b^-6*a^-1*b^-2*(b^-2*((b^-1*a^-1)^7*\
    b^-6*a^-1)^2)^2*((b^-1*a^-1)^7*b^-6*a^-1)^3*a^-2*b^-1*(b^-1*a^-1)^2*(a^-1*b^-3)^2*(a^-1*\
    b^-1)^4*b^-1*a^-1*b^-2*a^-2*b^-2*(b^-3*a^-1)^2*b^-1*(b^-1*a^-1*b^4*(a^-1*b^-1)^7*b^-5*a^\
    -1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*(b^-1\
    *a^-1)^2*a^-3*b^-4*a^-2*b^-1*a^-1)^3*b^-1*(a^-1*((a^-1*b^-1)^7*b^-5*a^-1*b^-2*(b^-1*a^-1\
    )^7*b^-6*a^-1*b^-1)^2*(a^-1*b^-1)^7*b^-5*a^-1*b^-4*((b^-1*a^-1)^7*b^-6*a^-1)^2*a^-1*b^-2\
    *(a^-1*b^-1*a^-1)^2*b^-7*a^-3*b^-1*a^-1)^4*a^-1*b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^-1\
    *b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3*b\
    ^-4*a^-1*(a^-1*b^-1)^2*a^-1*b^-10*(a^-1*b^-1)^7*b^-5*a^-1*b^-2*((b^-1*a^-1)^7*b^-6*a^-1*\
    b^-2*(b^-1*a^-1)^7*b^-6*a^-1)^2*b^-2*a^-2*b^-1*(b^-1*a^-1)^2*(a^-1*b^-3)^2*(a^-1*b^-1)^3\
    *a^-2*(a^-2*b^-1)^2*(b^-1*a^-1)^2*b^-2*a^-1",
    "a*b^3*(a*b*a)^2*(a*b)^6*b^2*a*b^3*a*(a*b)^2*b*a*(a*b^6)^2*(a*b)^6*a*(b*a*b^5*(b*a)^7*b^2\
    )^2*b^3*a*b^5*(b*a)^7*b^-6*a^2*b*a^3*b^7*(a*b*a)^2*b^2*a*(a*b^5*(b*a)^7*b)^2*b*(b^2*(b*a\
    *b^5*(b*a)^7)^2)^2*b^3*a*b^5*(b*a)^7*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)\
    ^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^2*a^2*b*a^3*b^7*(a*b*a)^2*b^2*a*(a*b\
    ^5*(b*a)^7*b)^2*b*(b^2*(b*a*b^5*(b*a)^7)^2)^2*b^3*a*b^5*(b*a)^7*b^-1"),
   (1, "b^2*a^6*(b*a*b^5*(b*a)^7*b^8)^2*b*a*b^5*(b*a)^7*b^10*(a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b\
    ^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4*a^2*b*a^3*b^7*(a*b*a)^\
    2*b^2*a*(a*b^5*(b*a)^7*b)^2*b*(b^2*(b*a*b^5*(b*a)^7)^2)^2*b^3*a*b^5*(b*a)^7*((a*b)^2*a^2\
    *b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-\
    4)^8*b^-1*(a*b)^2*a^2*b^4*a^3*b^2*a*b*a^-1*(b*a)^2*(b*a*b^2)^2*b*a*(a*b)^2*b*a^3*b^5*(b*\
    a)^7*b^2*(b*a*b^5*(b*a)^7)^3*b^4*(b*a*b^5*(b*a)^7)^5*b^8*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^\
    3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4*a^2*b*a^3*b^7*(a*\
    b*a)^2*b^2*a*(a*b^5*(b*a)^7*b)^2*b*(b^2*(b*a*b^5*(b*a)^7)^2)^2*b^3*a*b^5*(b*a)^7*(a*b)^2\
    *a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7\
    *b^-4)^2*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b\
    ^11*a*b^5*(b*a)^7*b^-4)^6*b^-1",
    "a*(a*b)^2*b^3*a^3*b*((b*a)^3*b^5*(b*a)^5)^2*(b*a)^2*b^2*(b*a*b^5*(b*a)^7)^4*b^3*a*b^5*(b\
    *a)^7*b^2*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*\
    b^11*a*b^5*(b*a)^7*b^-4)^4*a^2*b*a^3*b^7*(a*b*a)^2*b^2*a*(a*b^5*(b*a)^7*b)^2*b*(b^2*(b*a\
    *b^5*(b*a)^7)^2)^2*b^3*a*b^5*(b*a)^7*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)\
    ^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^5*b^-1"),
   (2, "a*b^2*(b*a^2*b*a)^3*b*a*(b*a*b^2)^2*b*a^2*b*(a*b^2*a)^2*b^5*(b*a)^7*((b*a*b^5*(b*a)^7)^2\
    *b^2)^2*(b*a*b^5*(b*a)^7)^2*(a^2*b*a^3*b^7*(a*b*a)^2*b^2*a*(a*b^5*(b*a)^7*b)^2*b*(b^2*(b\
    *a*b^5*(b*a)^7)^2)^2*b^3*a*b^5*(b*a)^7*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*\
    a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^3)^2*(a*b)^2*a^2*b^4*a^3*(a*b)^2*b\
    ^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4*a*(b^2*a*b)^2*b^\
    4*a^2*b^2*a*b*(b*a)^4*(b^3*a)^2*(a*b)^2*b*a^2*(a*b^5*(b*a)^7*b)^2*a*b^5*(b*a)^7*((b*a*b^\
    5*(b*a)^7)^2*b^2)^2*b^3*a*b^5*(b*a)^7*b^2*(a^2*b*a^3*b^7*(a*b*a)^2*b^2*a*(a*b^5*(b*a)^7*\
    b)^2*b*(b^2*(b*a*b^5*(b*a)^7)^2)^2*b^3*a*b^5*(b*a)^7*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*\
    b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^3)^2*((a*b)^2*a^2*b^\
    4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^\
    2*b^-1",
    "a*b*a^8*b*(b*a)^2*b^10*a*b^5*(b*a)^7*b^2*(b*a*b^5*(b*a)^7)^2*(b*a*b^5*(b*a)^7*b^2)^2*b^2\
    *(a^2*b*a^3*b^7*(a*b*a)^2*b^2*a*(a*b^5*(b*a)^7*b)^2*b*(b^2*(b*a*b^5*(b*a)^7)^2)^2*b^3*a*\
    b^5*(b*a)^7*(a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2\
    *b^11*a*b^5*(b*a)^7*b^-4)^2*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b\
    *a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^2*b^-1*(a*b)^2*a^2*b^4*a^3*b^2*a*b*a^-1*(b*a)\
    ^2*(b*a*b^2)^2*b*a*(a*b)^2*b*a^3*b^5*(b*a)^7*b^2*(b*a*b^5*(b*a)^7)^3*b^4*(b*a*b^5*(b*a)^\
    7)^5*b^8*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b\
    ^11*a*b^5*(b*a)^7*b^-4*a^2*b*a^3*b^7*(a*b*a)^2*b^2*a*(a*b^5*(b*a)^7*b)^2*b*(b^2*(b*a*b^5\
    *(b*a)^7)^2)^2*b^3*a*b^5*(b*a)^7*(a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^\
    4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^2*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1\
    *a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^6*b^-1"),
   (1, "b*(b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7\
    *b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2*a^-1)^10*((a^-1*b^-1)^\
    7*b^-5*a^-1*b^-2*(b^-1*a^-1)^7*b^-6*a^-1*b^-1)^2*(a^-1*b^-1)^7*b^-5*a^-1*b^-4*((b^-1*a^-\
    1)^7*b^-6*a^-1)^2*a^-1*b^-2*(a^-1*b^-1*a^-1)^2*b^-7*a^-3*b^-1*a^-2*b^4*(a^-1*b^-1)^7*b^-\
    5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*(\
    b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2*a^-1*b^4*((a^-1*b^-1)^7*b^-5*a^-1*b^-3)^2*b^-3\
    *((b^-1*a^-1)^7*b^-6*a^-1)^5*a^-2*b^-1*(b^-1*a^-1)^2*(a^-1*b^-3)^2*a^-1*b^-1*a^-1*(b^-1*\
    a^-1*b^-1)^2*a^-2*b^-1*a^-3*(a^-1*b^-1)^3*b^-1",
    "b*(b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7\
    *b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2*a^-1)^8*((a^-1*b^-1)^7\
    *b^-5*a^-1*b^-2*(b^-1*a^-1)^7*b^-6*a^-1*b^-1)^2*(a^-1*b^-1)^7*b^-5*a^-1*b^-4*((b^-1*a^-1\
    )^7*b^-6*a^-1)^2*a^-1*b^-2*(a^-1*b^-1*a^-1)^2*b^-7*a^-3*b^-1*a^-2*b^4*(a^-1*b^-1)^7*b^-5\
    *a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*(b\
    ^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2*a^-1*((a^-1*b^-1)^7*b^-5*a^-1*b^-2*(b^-1*a^-1)^\
    7*b^-6*a^-1*b^-1)^2*(a^-1*b^-1)^7*b^-5*a^-1*b^-4*((b^-1*a^-1)^7*b^-6*a^-1)^2*a^-1*b^-2*(\
    a^-1*b^-1*a^-1)^2*b^-7*a^-1*(a^-2*b^-1)^2*(b^-1*a^-1)^7*b^-6*a^-1*b^-2*((b^-1*a^-1)^7*b^\
    -6*a^-1)^5*b^-2*(b^-1*a^-1)^7*b^-6*(a^-1*b^-2*a^-1)^2*b^-1*a^-1*(a^-1*b^-3)^2*(a^-1*b^-1\
    )^3*b^-1*a^-6*b^-1*(b^-2*a^-1)^2*b^-1*a^-1"),
   (1, "a^2*b^-1*a^-1*b^4*(b*a)^7*b^2*(b*a*b^5*(b*a)^7)^4*b^8*(b*a*b^5*(b*a)^7)^2*b^-4*(b^-4*(a*\
    b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*\
    a)^7)^6*b^-5",
    "b^5*a*(a^3*b)^2*a^2*(a*b^5*(b*a)^7*b)^2*b^2*a*b^5*(b*a)^7*b^11*a*b^5*(b*a)^8*b^5*(b*a)^7\
    *(a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5\
    *(b*a)^7*b^-4*(a^2*b*a^3*b^7*(a*b*a)^2*b^2*a*(a*b^5*(b*a)^7*b)^2*b*(b^2*(b*a*b^5*(b*a)^7\
    )^2)^2*b^3*a*b^5*(b*a)^7)^3*b^-1"),
   (1, "b^3*a*b^4*(b*a^2)^2*a*(a*b)^4*b^2*a*b^3*a*(a*b)^2*b*a^2*b^10*a*b^5*(b*a)^7*(b^3*a*b^5*(b\
    *a)^7*b^2)^2*b*a*b^5*(b*a)^7*b^-6*a^2*b*a^3*b^7*(a*b*a)^2*b^2*a*(a*b^5*(b*a)^7*b)^2*b*(b\
    ^2*(b*a*b^5*(b*a)^7)^2)^2*b^3*a*b^5*(b*a)^7*(a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5\
    *(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4*a^2*b*a^3*b^7*(a*b*a)^2*b^2*a*(\
    a*b^5*(b*a)^7*b)^2*b*(b^2*(b*a*b^5*(b*a)^7)^2)^2*b^3*a*b^5*(b*a)^7*b^-1*(a*b)^2*a^2*b^4*\
    a^3*b^2*a*b*a^-1*(b*a)^2*(b*a*b^2)^2*b*a*(a*b)^2*b*a^3*b^5*(b*a)^7*b^2*(b*a*b^5*(b*a)^7)\
    ^3*b^4*(b*a*b^5*(b*a)^7)^5*b^8*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4\
    *(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4*a^2*b*a^3*b^7*(a*b*a)^2*b^2*a*(a*b^5*(b*a)^\
    7*b)^2*b*(b^2*(b*a*b^5*(b*a)^7)^2)^2*b^3*a*b^5*(b*a)^7*(a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a\
    *b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^2*((a*b)^2*a^2*b^4*\
    a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^6*\
    b^-1",
    "b*(b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7\
    *b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2*a^-1)^4*((a^-1*b^-1)^7\
    *b^-5*a^-1*b^-2*(b^-1*a^-1)^7*b^-6*a^-1*b^-1)^2*(a^-1*b^-1)^7*b^-5*a^-1*b^-4*((b^-1*a^-1\
    )^7*b^-6*a^-1)^2*a^-1*b^-2*(a^-1*b^-1*a^-1)^2*b^-7*a^-3*b^-1*a^-2*b^-12*((a^-1*b^-1)^7*b\
    ^-5*a^-1*b^-1)^2*b^-1*(b^-4*(b^-1*a^-1)^7*b^-6*a^-1)^2*b^-2*(b^-1*a^-1)^7*b^-6*a^-3*b^-1\
    *(b^-1*a^-1)^2*(a^-1*b^-3)^2*(a^-1*b^-1)^2*(a^-1*b^-1*a^-1)^2*a^-2*b^-1*(b^-1*a^-2)^2*(b\
    ^-1*a^-1)^2*a^-1"),
   (2, "b*(((a^-1*b^-1)^7*b^-5*a^-1*b^-2*(b^-1*a^-1)^7*b^-6*a^-1*b^-1)^2*(a^-1*b^-1)^7*b^-5*a^-1\
    *b^-4*((b^-1*a^-1)^7*b^-6*a^-1)^2*a^-1*b^-2*(a^-1*b^-1*a^-1)^2*b^-7*a^-3*b^-1*a^-2)^4*b^\
    -12*(((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-2)^2*(a^-1*b^-1)^7*b^-5*a^-1*b^-4*((b^-1*a^-1)^\
    7*b^-6*a^-1)^2*a^-2*b^-1*(b^-1*a^-1)^2*(a^-1*b^-3)^2*a^-1*((b^-1*a^-1)^3*b^-1)^2*b^-3*a^\
    -1",
    "b*a*b^2*a^8*(b*a*b)^2*a*(b*a*b^2)^2*b*a*(a*b)^2*b*a^3*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^\
    3*b^3*a*b^5*(b*a)^7*b^10*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*\
    b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^2*(a^2*b*a^3*b^7*(a*b*a)^2*b^2*a*(a*b^5*(b*a)^7*\
    b)^2*b*(b^2*(b*a*b^5*(b*a)^7)^2)^2*b^3*a*b^5*(b*a)^7)^4*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3\
    *a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^9*b^-1"),
   (1, "b^3*(b*a)^3*a^2*(a*b)^2*a*((a*b^5*(b*a)^7*b)^2*b^2)^2*(a*b^5*(b*a)^7*b)^2*a*b^5*(b*a)^7*\
    b^-8*(a^2*b*a^3*b^7*(a*b*a)^2*b^2*a*(a*b^5*(b*a)^7*b)^2*b*(b^2*(b*a*b^5*(b*a)^7)^2)^2*b^\
    3*a*b^5*(b*a)^7)^3*b^-1*(a*b)^2*a^2*b^4*a^3*b^2*a*b*a^-1*(b*a)^2*(b*a*b^2)^2*b*a*(a*b)^2\
    *b*a^3*b^5*(b*a)^7*b^2*(b*a*b^5*(b*a)^7)^3*b^4*(b*a*b^5*(b*a)^7)^5*b^8*((a*b)^2*a^2*b^4*\
    a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4*a^2\
    *b*a^3*b^7*(a*b*a)^2*b^2*a*(a*b^5*(b*a)^7*b)^2*b*(b^2*(b*a*b^5*(b*a)^7)^2)^2*b^3*a*b^5*(\
    b*a)^7*(a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11\
    *a*b^5*(b*a)^7*b^-4)^2*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^\
    5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^6*b^-1",
    "b*a^2*b*(b*a)^2*(b^3*a*b)^2*b^4*(b*a)^7*(b*a*b^5*(b*a)^7*b^2)^2*(b*a*b^5*(b*a)^7)^2*(b*a\
    *b^5*(b*a)^7*b^2)^2*b^2*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b\
    ^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^4*b^-1*(a*b)^2*a^2*b^4*a^3*b^2*a*b*a^-1*(b*a)^2*(\
    b*a*b^2)^2*b*a*(a*b)^2*b*a^3*b^5*(b*a)^7*b^2*(b*a*b^5*(b*a)^7)^3*b^4*(b*a*b^5*(b*a)^7)^5\
    *b^8*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*\
    a*b^5*(b*a)^7*b^-4*a^2*b*a^3*b^7*(a*b*a)^2*b^2*a*(a*b^5*(b*a)^7*b)^2*b*(b^2*(b*a*b^5*(b*\
    a)^7)^2)^2*b^3*a*b^5*(b*a)^7*(a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b\
    *a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^2*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b\
    ^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^6*b^-1"),
   (2, "b*(b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7\
    *b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2*a^-1)^10*((a^-1*b^-1)^\
    7*b^-5*a^-1*b^-2*(b^-1*a^-1)^7*b^-6*a^-1*b^-1)^2*(a^-1*b^-1)^7*b^-5*a^-1*b^-4*((b^-1*a^-\
    1)^7*b^-6*a^-1)^2*a^-1*b^-2*(a^-1*b^-1*a^-1)^2*b^-7*a^-3*b^-1*a^-1*(a^-1*b^4*(a^-1*b^-1)\
    ^7*b^-5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*\
    b^-3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2)^2*a^-1*((a^-1*b^-1)^7*b^-5*a^-1*b^-2*(b\
    ^-1*a^-1)^7*b^-6*a^-1*b^-1)^2*(a^-1*b^-1)^7*b^-5*a^-1*b^-4*((b^-1*a^-1)^7*b^-6*a^-1)^2*a\
    ^-1*b^-2*(a^-1*b^-1*a^-1)^2*b^-7*a^-3*b^-1*a^-2*b^-10*(a^-1*b^-1)^7*b^-4*(b^-1*a^-1)^8*b\
    ^-6*a^-1*((b^-1*a^-1)^7*b^-6*a^-1*b^-2)^3*b^-2*((b^-1*a^-1)^7*b^-6*a^-1)^3*a^-2*b^-1*(b^\
    -1*a^-1)^2*(a^-1*b^-3)^2*(a^-1*b^-1)^3*a^-2*b^-3*a^-1*(a^-1*b^-1)^2*a^-4",
    "a^2*(a*b)^2*b^4*a*b*(b*a)^5*(b^3*a)^2*(a*b)^2*b*a^2*(a*b^5*(b*a)^7*b^3)^4*a*b^5*(b*a)^7*\
    b^-8*(a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a\
    *b^5*(b*a)^7*b^-4*a^2*b*a^3*b^7*(a*b*a)^2*b^2*a*(a*b^5*(b*a)^7*b)^2*b*(b^2*(b*a*b^5*(b*a\
    )^7)^2)^2*b^3*a*b^5*(b*a)^7*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b\
    *a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^4*a*(b^2*a*b)^2*b^4*a^2*b^2*a*b*(b*a)^4*(b^3*\
    a)^2*(a*b)^2*b*a^2*(a*b^5*(b*a)^7*b)^2*a*b^5*(b*a)^7*((b*a*b^5*(b*a)^7)^2*b^2)^2*b^3*a*b\
    ^5*(b*a)^7*b^2*(a^2*b*a^3*b^7*(a*b*a)^2*b^2*a*(a*b^5*(b*a)^7*b)^2*b*(b^2*(b*a*b^5*(b*a)^\
    7)^2)^2*b^3*a*b^5*(b*a)^7*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a\
    *b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^3)^2*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*\
    b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^2*b^-1"),
   (2, "b^4*a*b^3*((a*b)^2*a)^2*(b*a*b^2)^2*b*a*(a*b)^2*b*a^3*b^5*(b*a)^7*b^2*(b^3*a*b^5*(b*a)^7\
    )^2*b^3*(b^6*a)^2*(b*a)^6*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a\
    *b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^2*a^2*b*a^3*b^7*(a*b*a)^2*b^2*a*(a*b^5*(b*a)^7*\
    b)^2*b*(b^2*(b*a*b^5*(b*a)^7)^2)^2*b^3*a*b^5*(b*a)^7*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*\
    b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^4*b^-1",
    "b*(b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7\
    *b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2*a^-1)^2*b^4*(a^-1*b^-1\
    )^7*b^-5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1\
    *b^-3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2*(a^-1*((a^-1*b^-1)^7*b^-5*a^-1*b^-2*(b^\
    -1*a^-1)^7*b^-6*a^-1*b^-1)^2*(a^-1*b^-1)^7*b^-5*a^-1*b^-4*((b^-1*a^-1)^7*b^-6*a^-1)^2*a^\
    -1*b^-2*(a^-1*b^-1*a^-1)^2*b^-7*a^-3*b^-1*a^-1)^3*(a^-1*b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-1\
    1*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^\
    2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2)^3*a^-1*(((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-2)^2*b^-3*(b\
    ^-1*a^-1)^7*b^-6*a^-3*b^-1*(b^-1*a^-1)^2*(a^-1*b^-3)^2*(a^-1*b^-1)^4*b^-1*a^-3*b^-3*(b^-\
    1*a^-2)^2"),
   (2, "(a*b*a)^2*a*b^4*a^8*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^4*b^3*a*b^5*(b*a)^7*b^8*((a*b)^2*a\
    ^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b\
    ^-4)^8*b^-1",
    "b^5*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^\
    -6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2*a^-1*b^4*(a^-1*b^-1)^7*b^\
    -5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*\
    (b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2*((a^-1*b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^\
    -1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3\
    *b^-4*a^-1*(a^-1*b^-1)^2)^3*a^-1*((a^-1*b^-1)^7*b^-5*a^-1*b^-2*(b^-1*a^-1)^7*b^-6*a^-1*b\
    ^-1)^2*(a^-1*b^-1)^7*b^-5*a^-1*b^-4*((b^-1*a^-1)^7*b^-6*a^-1)^2*a^-1*b^-2*(a^-1*b^-1*a^-\
    1)^2*b^-7*a^-3*b^-1*a^-1)^2*a^-1*b^-1*(b^-1*a^-1)^7*b^-6*a^-1*b^-2*(b^-2*((b^-1*a^-1)^7*\
    b^-6*a^-1)^2)^2*((b^-1*a^-1)^7*b^-6*a^-1)^3*a^-2*b^-1*(b^-1*a^-1)^2*(a^-1*b^-3)^2*(a^-1*\
    b^-1)^4*b^-1*a^-1*b^-2*a^-2*b^-2*(b^-3*a^-1)^2*b^-2*(a^-1*((a^-1*b^-1)^7*b^-5*a^-1*b^-2*\
    (b^-1*a^-1)^7*b^-6*a^-1*b^-1)^2*(a^-1*b^-1)^7*b^-5*a^-1*b^-4*((b^-1*a^-1)^7*b^-6*a^-1)^2\
    *a^-1*b^-2*(a^-1*b^-1*a^-1)^2*b^-7*a^-3*b^-1*a^-1)^2*(a^-1*b^4*(a^-1*b^-1)^7*b^-5*a^-1*b\
    ^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-\
    1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2)^3*a^-1*b^6*(a^-1*b^-1)^7*b^-5*a^-1*b^-2*((b^-1*a^-1)^\
    7*b^-6*a^-1)^2*(b^-2*a^-1*b^-1)^2*b^-1*a^-3*b^-3*a^-2"),
   (2, "b*(b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7\
    *b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2*a^-1)^4*b^4*(a^-1*b^-1\
    )^7*b^-5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1\
    *b^-3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2*((a^-1*b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-1\
    1*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^\
    2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2)^2*a^-1*((a^-1*b^-1)^7*b^-5*a^-1*b^-2*(b^-1*a^-1)^7*b^-6*\
    a^-1*b^-1)^2*(a^-1*b^-1)^7*b^-5*a^-1*b^-4*((b^-1*a^-1)^7*b^-6*a^-1)^2*a^-1*b^-2*(a^-1*b^\
    -1*a^-1)^2*b^-7*a^-3*b^-1*a^-1)^2*a^-1*b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^-1*b^-1)^7*\
    b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*\
    (a^-1*b^-1)^3*b^-6*((b^-1*a^-1)^7*b^-6*a^-1)^5*b^-4*((b^-1*a^-1)^7*b^-6*a^-1)^3*b^-2*(b^\
    -1*a^-1)^7*b^-6*a^-3*b^-1*(b^-1*a^-1)^2*(a^-1*b^-3)^2*(a^-1*b^-1)^3*a*b^-1*a^-1*b^-2*a^-\
    3*b^-4*a^-1*(a^-1*b^-1)^2*a^-1*b*((a^-1*b^-1)^7*b^-5*a^-1*b^-2*(b^-1*a^-1)^7*b^-6*a^-1*b\
    ^-1)^2*(a^-1*b^-1)^7*b^-5*a^-1*b^-4*((b^-1*a^-1)^7*b^-6*a^-1)^2*a^-1*b^-2*(a^-1*b^-1*a^-\
    1)^2*b^-7*a^-3*b^-1*a^-2*b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1\
    )^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2*\
    a^-1*((a^-1*b^-1)^7*b^-5*a^-1*b^-2*(b^-1*a^-1)^7*b^-6*a^-1*b^-1)^2*(a^-1*b^-1)^7*b^-5*a^\
    -1*b^-4*((b^-1*a^-1)^7*b^-6*a^-1)^2*a^-1*b^-2*(a^-1*b^-1*a^-1)^2*b^-7*a^-1*(a^-2*b^-1)^2\
    *b^-6*(b^-1*a^-1)^7*b^-6*a^-1*((b^-1*a^-1)^7*b^-6*a^-1*b^-2)^2*((b^-1*a^-1)^7*b^-6*a^-1)\
    ^3*b^-4*a^-2*b^-1*(b^-1*a^-1)^2*(a^-1*b^-3)^2*a^-1*b^-1*a^-1*(b^-1*a^-1*b^-1)^2*(a^-2*b^\
    -1*a^-1)^3*a^-1",
    "b^5*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^\
    -6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2*a^-1*b^4*(a^-1*b^-1)^7*b^\
    -5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*\
    (b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2*((a^-1*b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^\
    -1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3\
    *b^-4*a^-1*(a^-1*b^-1)^2)^3*a^-1*((a^-1*b^-1)^7*b^-5*a^-1*b^-2*(b^-1*a^-1)^7*b^-6*a^-1*b\
    ^-1)^2*(a^-1*b^-1)^7*b^-5*a^-1*b^-4*((b^-1*a^-1)^7*b^-6*a^-1)^2*a^-1*b^-2*(a^-1*b^-1*a^-\
    1)^2*b^-7*a^-3*b^-1*a^-1)^2*a^-1*b^-1*(b^-1*a^-1)^7*b^-6*a^-1*b^-2*(b^-2*((b^-1*a^-1)^7*\
    b^-6*a^-1)^2)^2*((b^-1*a^-1)^7*b^-6*a^-1)^3*a^-2*b^-1*(b^-1*a^-1)^2*(a^-1*b^-3)^2*(a^-1*\
    b^-1)^4*b^-1*a^-1*b^-2*a^-2*b^-2*(b^-3*a^-1)^2*b^-1*(b^-1*a^-1*b^4*(a^-1*b^-1)^7*b^-5*a^\
    -1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*(b^-1\
    *a^-1)^2*a^-3*b^-4*a^-2*b^-1*a^-1)^2*b^-1*a^-1*((a^-1*b^-1)^7*b^-5*a^-1*b^-2*(b^-1*a^-1)\
    ^7*b^-6*a^-1*b^-1)^2*(a^-1*b^-1)^7*b^-5*a^-1*b^-4*((b^-1*a^-1)^7*b^-6*a^-1)^2*a^-1*b^-2*\
    (a^-1*b^-1*a^-1)^2*b^-7*a^-3*b^-1*a^-1*(a^-1*b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^-1*b^\
    -1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3*b^-4\
    *a^-1*(a^-1*b^-1)^2)^2*a^-1*b^8*(a^-1*b^-1)^7*b^-5*a^-1*b^-4*((b^-1*a^-1)^7*b^-6*a^-1)^2\
    *((b^-1*a^-1)^7*b^-6*a^-1*b^-2)^4*a^-2*b^-1*(b^-1*a^-1)^2*(a^-1*b^-3)^2*(a^-1*b^-1)^5*(b\
    ^-3*a^-2)^2*b^-2*a^-1"),
   (2, "a*b^2*a^7*b^2*a*(a*b)^5*b^2*a*b^3*a*(a*b)^2*b*a^2*b^10*a*b^5*(b*a)^8*b^5*(b*a)^7*((b*a*b\
    ^5*(b*a)^7)^2*b^2)^2*b^4*(a^2*b*a^3*b^7*(a*b*a)^2*b^2*a*(a*b^5*(b*a)^7*b)^2*b*(b^2*(b*a*\
    b^5*(b*a)^7)^2)^2*b^3*a*b^5*(b*a)^7)^4*(a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a\
    )^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4*a^2*b*a^3*b^7*(a*b*a)^2*b^2*a*(a*b^5\
    *(b*a)^7*b)^2*b*(b^2*(b*a*b^5*(b*a)^7)^2)^2*b^3*a*b^5*(b*a)^7*((a*b)^2*a^2*b^4*a^3*(a*b)\
    ^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^6*b^-1*(a*b\
    )^2*a^2*b^4*a^3*b^2*a*b*a^-1*(b*a)^2*(b*a*b^2)^2*b*a*(a*b)^2*b*a^3*b^5*(b*a)^7*b^2*(b*a*\
    b^5*(b*a)^7)^3*b^4*(b*a*b^5*(b*a)^7)^5*b^8*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5\
    *(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4*a^2*b*a^3*b^7*(a*b*a)^2*b^2*a*(\
    a*b^5*(b*a)^7*b)^2*b*(b^2*(b*a*b^5*(b*a)^7)^2)^2*b^3*a*b^5*(b*a)^7*(a*b)^2*a^2*b^4*a^3*(\
    a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^2*((a*b\
    )^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a\
    )^7*b^-4)^6*b^-1",
    "b^5*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^\
    -6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2*a^-1*b^4*(a^-1*b^-1)^7*b^\
    -5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*\
    (b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2*((a^-1*b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^\
    -1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3\
    *b^-4*a^-1*(a^-1*b^-1)^2)^3*a^-1*((a^-1*b^-1)^7*b^-5*a^-1*b^-2*(b^-1*a^-1)^7*b^-6*a^-1*b\
    ^-1)^2*(a^-1*b^-1)^7*b^-5*a^-1*b^-4*((b^-1*a^-1)^7*b^-6*a^-1)^2*a^-1*b^-2*(a^-1*b^-1*a^-\
    1)^2*b^-7*a^-3*b^-1*a^-1)^2*a^-1*b^-1*(b^-1*a^-1)^7*b^-6*a^-1*b^-2*(b^-2*((b^-1*a^-1)^7*\
    b^-6*a^-1)^2)^2*((b^-1*a^-1)^7*b^-6*a^-1)^3*a^-2*b^-1*(b^-1*a^-1)^2*(a^-1*b^-3)^2*(a^-1*\
    b^-1)^4*b^-1*a^-1*b^-2*a^-2*b^-2*(b^-3*a^-1)^2*b^-1*(b^-1*a^-1*b^4*(a^-1*b^-1)^7*b^-5*a^\
    -1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*(b^-1\
    *a^-1)^2*a^-3*b^-4*a^-2*b^-1*a^-1)^5*b^-1*((a^-1*b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^-\
    1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3*\
    b^-4*a^-1*(a^-1*b^-1)^2)^2*a^-1*((a^-1*b^-1)^7*b^-5*a^-1*b^-2*(b^-1*a^-1)^7*b^-6*a^-1*b^\
    -1)^2*(a^-1*b^-1)^7*b^-5*a^-1*b^-4*((b^-1*a^-1)^7*b^-6*a^-1)^2*a^-1*b^-2*(a^-1*b^-1*a^-1\
    )^2*b^-7*a^-3*b^-1*a^-1)^2*a^-1*b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^\
    -1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b\
    ^-1)^3*b^-6*((b^-1*a^-1)^7*b^-6*a^-1)^5*b^-4*((b^-1*a^-1)^7*b^-6*a^-1)^3*b^-2*(b^-1*a^-1\
    )^7*b^-6*a^-3*b^-1*(b^-1*a^-1)^2*(a^-1*b^-3)^2*(a^-1*b^-1)^3*a*b^-1*a^-1*b^-2*a^-3*b^-4*\
    a^-1*(a^-1*b^-1)^2*a^-1*b*((a^-1*b^-1)^7*b^-5*a^-1*b^-2*(b^-1*a^-1)^7*b^-6*a^-1*b^-1)^2*\
    (a^-1*b^-1)^7*b^-5*a^-1*b^-4*((b^-1*a^-1)^7*b^-6*a^-1)^2*a^-1*b^-2*(a^-1*b^-1*a^-1)^2*b^\
    -7*a^-3*b^-1*a^-2*b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-\
    3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2*(a^-1*(\
    (a^-1*b^-1)^7*b^-5*a^-1*b^-2*(b^-1*a^-1)^7*b^-6*a^-1*b^-1)^2*(a^-1*b^-1)^7*b^-5*a^-1*b^-\
    4*((b^-1*a^-1)^7*b^-6*a^-1)^2*a^-1*b^-2*(a^-1*b^-1*a^-1)^2*b^-7*a^-3*b^-1*a^-1)^3*a^-1*b\
    ^-3*(b^-1*a^-1)^7*b^-6*a^-1*((b^-1*a^-1)^7*b^-6*a^-1*b^-2)^2*b^-4*((b^-1*a^-1)^7*b^-6*a^\
    -1)^3*b^-2*(b^-1*a^-1)^7*b^-6*a^-3*b^-1*(b^-1*a^-1)^2*(a^-1*b^-3)^2*(a^-1*b^-1)^3*a^-6*(\
    a^-2*b^-1)^2*(b^-1*a^-1)^2"),
   (0, "b^2*a^2*(b^2*a^2*b)^2*(b*a)^4*(b^3*a)^2*(a*b)^2*b*a^3*b^5*(b*a)^7*b^6*(b*a*b^5*(b*a)^7)^\
    3*b^2*(b^3*a*b^5*(b*a)^7)^2*b^-8*a^2*b*a^3*b^7*(a*b*a)^2*b^2*a*(a*b^5*(b*a)^7*b)^2*b*(b^\
    2*(b*a*b^5*(b*a)^7)^2)^2*b^3*a*b^5*(b*a)^7*(a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*\
    (b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4*(a^2*b*a^3*b^7*(a*b*a)^2*b^2*a*(\
    a*b^5*(b*a)^7*b)^2*b*(b^2*(b*a*b^5*(b*a)^7)^2)^2*b^3*a*b^5*(b*a)^7)^3*b^-1*(a*b)^2*a^2*b\
    ^4*a^3*b^2*a*b*a^-1*(b*a)^2*(b*a*b^2)^2*b*a*(a*b)^2*b*a^3*b^5*(b*a)^7*b^2*(b*a*b^5*(b*a)\
    ^7)^3*b^4*(b*a*b^5*(b*a)^7)^5*b^8*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*\
    b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4*a^2*b*a^3*b^7*(a*b*a)^2*b^2*a*(a*b^5*(b*\
    a)^7*b)^2*b*(b^2*(b*a*b^5*(b*a)^7)^2)^2*b^3*a*b^5*(b*a)^7*(a*b)^2*a^2*b^4*a^3*(a*b)^2*b^\
    3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^2*((a*b)^2*a^2*b\
    ^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)\
    ^6*b^-1",
    "b^5*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^\
    -6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2*a^-1*((a^-1*b^-1)^7*b^-5*\
    a^-1*b^-2*(b^-1*a^-1)^7*b^-6*a^-1*b^-1)^2*(a^-1*b^-1)^7*b^-5*a^-1*b^-4*((b^-1*a^-1)^7*b^\
    -6*a^-1)^2*a^-1*b^-2*(a^-1*b^-1*a^-1)^2*b^-7*a^-3*b^-1*a^-1*(a^-1*b^4*(a^-1*b^-1)^7*b^-5\
    *a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*(b\
    ^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2)^3*a^-1*b^-12*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^3*\
    b^-1*(b^-2*(b^-1*a^-1)^7*b^-6*a^-1)^2*b^-3*(b^-1*a^-2)^2*a^-2*b^-2*(b^-1*a^-1)^3*b^-1"),
   (2, "(a*b*(a*b*a)^2)^2*b*a*(b*a*b^2)^2*b*a*(a*b)^2*b*a^2*(a*b^5*(b*a)^7*b)^2*a*b^5*(b*a)^7*(b\
    ^3*a*b^5*(b*a)^7*b^4)^2*b^3*a*b^5*(b*a)^7*b^-8*a^2*b*a^3*b^7*(a*b*a)^2*b^2*a*(a*b^5*(b*a\
    )^7*b)^2*b*(b^2*(b*a*b^5*(b*a)^7)^2)^2*b^3*a*b^5*(b*a)^7*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^\
    3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^9*b^-1",
    "a*b*a*(a*b)^9*b^2*a*b^3*a*(a*b)^2*b*a^2*(a*b^5*(b*a)^7*b)^2*a*b^5*(b*a)^7*b^-8*((a*b)^2*\
    a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*\
    b^-4*a^2*b*a^3*b^7*(a*b*a)^2*b^2*a*(a*b^5*(b*a)^7*b)^2*b*(b^2*(b*a*b^5*(b*a)^7)^2)^2*b^3\
    *a*b^5*(b*a)^7)^2*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*\
    a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^5*b^-1*(a*b)^2*a^2*b^4*a^3*b^2*a*b*a^-1*(b*a)^2*(b*a*b^\
    2)^2*b*a*(a*b)^2*b*a^3*b^5*(b*a)^7*b^2*(b*a*b^5*(b*a)^7)^3*b^4*(b*a*b^5*(b*a)^7)^5*b^8*(\
    (a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*\
    (b*a)^7*b^-4*a^2*b*a^3*b^7*(a*b*a)^2*b^2*a*(a*b^5*(b*a)^7*b)^2*b*(b^2*(b*a*b^5*(b*a)^7)^\
    2)^2*b^3*a*b^5*(b*a)^7*(a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5\
    *(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^2*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*\
    a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^6*b^-1"),
   (2, "(a^2*b)^2*a*b^3*a^2*b^5*(b*a)^7*(b*a*b^5*(b*a)^7*b^2)^2*b^2*(b*a*b^5*(b*a)^7)^4*((a*b)^2\
    *a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7\
    *b^-4)^2*a^2*b*a^3*b^7*(a*b*a)^2*b^2*a*(a*b^5*(b*a)^7*b)^2*b*(b^2*(b*a*b^5*(b*a)^7)^2)^2\
    *b^3*a*b^5*(b*a)^7*a*(b^2*a*b)^2*b^4*a^2*b^2*a*b*(b*a)^4*(b^3*a)^2*(a*b)^2*b*a^2*(a*b^5*\
    (b*a)^7*b)^2*a*b^5*(b*a)^7*((b*a*b^5*(b*a)^7)^2*b^2)^2*b^3*a*b^5*(b*a)^7*b^2*(a^2*b*a^3*\
    b^7*(a*b*a)^2*b^2*a*(a*b^5*(b*a)^7*b)^2*b*(b^2*(b*a*b^5*(b*a)^7)^2)^2*b^3*a*b^5*(b*a)^7*\
    ((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5\
    *(b*a)^7*b^-4)^3)^2*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(\
    b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^2*b^-1",
    "b*(b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7\
    *b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2*a^-1)^4*b^4*(a^-1*b^-1\
    )^7*b^-5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1\
    *b^-3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2*((a^-1*b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-1\
    1*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^\
    2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2)^2*a^-1*((a^-1*b^-1)^7*b^-5*a^-1*b^-2*(b^-1*a^-1)^7*b^-6*\
    a^-1*b^-1)^2*(a^-1*b^-1)^7*b^-5*a^-1*b^-4*((b^-1*a^-1)^7*b^-6*a^-1)^2*a^-1*b^-2*(a^-1*b^\
    -1*a^-1)^2*b^-7*a^-3*b^-1*a^-1)^2*a^-1*b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^-1*b^-1)^7*\
    b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*\
    (a^-1*b^-1)^3*b^-6*((b^-1*a^-1)^7*b^-6*a^-1)^5*b^-4*((b^-1*a^-1)^7*b^-6*a^-1)^3*b^-2*(b^\
    -1*a^-1)^7*b^-6*a^-3*b^-1*(b^-1*a^-1)^2*(a^-1*b^-3)^2*(a^-1*b^-1)^3*a*b^-1*a^-1*b^-2*a^-\
    3*b^-4*a^-1*(a^-1*b^-1)^2*a^-1*b*(b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*\
    a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1\
    *b^-1)^2*a^-1)^10*(((a^-1*b^-1)^7*b^-5*a^-1*b^-2*(b^-1*a^-1)^7*b^-6*a^-1*b^-1)^2*(a^-1*b\
    ^-1)^7*b^-5*a^-1*b^-4*((b^-1*a^-1)^7*b^-6*a^-1)^2*a^-1*b^-2*(a^-1*b^-1*a^-1)^2*b^-7*a^-3\
    *b^-1*a^-2)^2*b^8*((a^-1*b^-1)^7*b^-5*a^-1*b^-2*((b^-1*a^-1)^7*b^-6*a^-1)^2*b^-1)^2*b^-1\
    *(b^-1*a^-1)^7*b^-6*a^-8*b^-2*(b^-1*a^-1)^2*a^-2*b^-2"),
   (2, "(a*b)^2*a^2*b^2*(b^3*a)^2*b^2*(b*a*b^5*(b*a)^7)^2*b^3*a*b^5*(b*a)^7*(b^3*a*b^5*(b*a)^7*b\
    ^2)^2*(b*a*b^5*(b*a)^7)^2*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a\
    *b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^3*a^2*b*a^3*b^7*(a*b*a)^2*b^2*a*(a*b^5*(b*a)^7*\
    b)^2*b*(b^2*(b*a*b^5*(b*a)^7)^2)^2*b^3*a*b^5*(b*a)^7*a*(b^2*a*b)^2*b^4*a^2*b^2*a*b*(b*a)\
    ^4*(b^3*a)^2*(a*b)^2*b*a^2*(a*b^5*(b*a)^7*b)^2*a*b^5*(b*a)^7*((b*a*b^5*(b*a)^7)^2*b^2)^2\
    *b^3*a*b^5*(b*a)^7*b^2*(a^2*b*a^3*b^7*(a*b*a)^2*b^2*a*(a*b^5*(b*a)^7*b)^2*b*(b^2*(b*a*b^\
    5*(b*a)^7)^2)^2*b^3*a*b^5*(b*a)^7*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*\
    b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^3)^2*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a\
    *b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^2*b^-1",
    "b*a*b^4*a^2*(b^2*a*b)^2*(b*a)^2*(b*a*b^2)^2*b*a^2*b*(a*b^2*a)^2*b^5*(b*a)^7*b^4*(b*a*b^5\
    *(b*a)^7*b^3*a*b^5*(b*a)^7)^2*b^-2*(b^-4*(a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b\
    *a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4*a^2*b*a^3*b^7*(a*b*a)^2*b^2*a*(a*b\
    ^5*(b*a)^7*b)^2*b*(b^2*(b*a*b^5*(b*a)^7)^2)^2*b^3*a*b^5*(b*a)^7*(a*b)^2*a^2*b^4*a^3*(a*b\
    )^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7)^2*(b^-4*(a*b)^2\
    *a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7\
    )^6*b^-5*(a*b)^2*a^2*b^4*a^3*b^2*a*b*a^-1*(b*a)^2*(b*a*b^2)^2*b*a*(a*b)^2*b*a^3*b^5*(b*a\
    )^7*b^2*(b*a*b^5*(b*a)^7)^3*b^4*(b*a*b^5*(b*a)^7)^5*b^8*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3\
    *a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4*a^2*b*a^3*b^7*(a*b\
    *a)^2*b^2*a*(a*b^5*(b*a)^7*b)^2*b*(b^2*(b*a*b^5*(b*a)^7)^2)^2*b^3*a*b^5*(b*a)^7*(a*b)^2*\
    a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*\
    b^-4)^2*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^\
    11*a*b^5*(b*a)^7*b^-4)^6*b^-1"),
   (2, "b*(b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7\
    *b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2*a^-1)^4*b^4*(a^-1*b^-1\
    )^7*b^-5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1\
    *b^-3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2*((a^-1*b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-1\
    1*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^\
    2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2)^2*a^-1*((a^-1*b^-1)^7*b^-5*a^-1*b^-2*(b^-1*a^-1)^7*b^-6*\
    a^-1*b^-1)^2*(a^-1*b^-1)^7*b^-5*a^-1*b^-4*((b^-1*a^-1)^7*b^-6*a^-1)^2*a^-1*b^-2*(a^-1*b^\
    -1*a^-1)^2*b^-7*a^-3*b^-1*a^-1)^2*a^-1*b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^-1*b^-1)^7*\
    b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*\
    (a^-1*b^-1)^3*b^-6*((b^-1*a^-1)^7*b^-6*a^-1)^5*b^-4*((b^-1*a^-1)^7*b^-6*a^-1)^3*b^-2*(b^\
    -1*a^-1)^7*b^-6*a^-3*b^-1*(b^-1*a^-1)^2*(a^-1*b^-3)^2*(a^-1*b^-1)^3*a*b^-1*a^-1*b^-2*a^-\
    3*b^-4*a^-1*(a^-1*b^-1)^2*a^-1*b*(b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*\
    a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1\
    *b^-1)^2*a^-1*((a^-1*b^-1)^7*b^-5*a^-1*b^-2*(b^-1*a^-1)^7*b^-6*a^-1*b^-1)^2*(a^-1*b^-1)^\
    7*b^-5*a^-1*b^-4*((b^-1*a^-1)^7*b^-6*a^-1)^2*a^-1*b^-2*(a^-1*b^-1*a^-1)^2*b^-7*a^-3*b^-1\
    *a^-2)^2*(b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b^-1)^2*(a^-1*b^-1)^6*a^-1*(b^-6*a^-1*b^-1)^2*(a^\
    -1*b^-1)^6*b^-1*(b^-4*a^-1)^2*b^-1*a^-1*(a^-1*b^-1)^2*b^-1*a^-4*b^-1",
    "b^5*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^\
    -6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2*a^-1*b^4*(a^-1*b^-1)^7*b^\
    -5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*\
    (b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2*((a^-1*b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^\
    -1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3\
    *b^-4*a^-1*(a^-1*b^-1)^2)^3*a^-1*((a^-1*b^-1)^7*b^-5*a^-1*b^-2*(b^-1*a^-1)^7*b^-6*a^-1*b\
    ^-1)^2*(a^-1*b^-1)^7*b^-5*a^-1*b^-4*((b^-1*a^-1)^7*b^-6*a^-1)^2*a^-1*b^-2*(a^-1*b^-1*a^-\
    1)^2*b^-7*a^-3*b^-1*a^-1)^2*a^-1*b^-1*(b^-1*a^-1)^7*b^-6*a^-1*b^-2*(b^-2*((b^-1*a^-1)^7*\
    b^-6*a^-1)^2)^2*((b^-1*a^-1)^7*b^-6*a^-1)^3*a^-2*b^-1*(b^-1*a^-1)^2*(a^-1*b^-3)^2*(a^-1*\
    b^-1)^4*b^-1*a^-1*b^-2*a^-2*b^-2*(b^-3*a^-1)^2*b^-1*(b^-1*a^-1*b^4*(a^-1*b^-1)^7*b^-5*a^\
    -1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*(b^-1\
    *a^-1)^2*a^-3*b^-4*a^-2*b^-1*a^-1)^3*b^-1*(a^-1*b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^-1\
    *b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3*b\
    ^-4*a^-1*(a^-1*b^-1)^2*a^-1*((a^-1*b^-1)^7*b^-5*a^-1*b^-2*(b^-1*a^-1)^7*b^-6*a^-1*b^-1)^\
    2*(a^-1*b^-1)^7*b^-5*a^-1*b^-4*((b^-1*a^-1)^7*b^-6*a^-1)^2*a^-1*b^-2*(a^-1*b^-1*a^-1)^2*\
    b^-7*a^-3*b^-1*a^-1)^2*a^-1*b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b\
    ^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)\
    ^3*b^-2*(((b^-1*a^-1)^7*b^-6*a^-1*b^-2)^2*(b^-1*a^-1)^7*b^-6*a^-1)^2*((b^-1*a^-1)^7*b^-6\
    *a^-1)^2*b^-2*a^-1*b^-2*(a^-1*b^-2*a^-1)^2*(a^-1*b^-1)^2"),
   (2, "a*b^2*(b*a)^2*a*(a*b)^4*(b^2*(b*a*b^5*(b*a)^7)^3)^2*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b\
    ^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^3*a^2*b*a^3*b^7*(a*b*\
    a)^2*b^2*a*(a*b^5*(b*a)^7*b)^2*b*(b^2*(b*a*b^5*(b*a)^7)^2)^2*b^3*a*b^5*(b*a)^7*((a*b)^2*\
    a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*\
    b^-4)^4*b^-1",
    "b^5*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^\
    -6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2*a^-1*b^4*(a^-1*b^-1)^7*b^\
    -5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*\
    (b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2*((a^-1*b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^\
    -1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3\
    *b^-4*a^-1*(a^-1*b^-1)^2)^3*a^-1*((a^-1*b^-1)^7*b^-5*a^-1*b^-2*(b^-1*a^-1)^7*b^-6*a^-1*b\
    ^-1)^2*(a^-1*b^-1)^7*b^-5*a^-1*b^-4*((b^-1*a^-1)^7*b^-6*a^-1)^2*a^-1*b^-2*(a^-1*b^-1*a^-\
    1)^2*b^-7*a^-3*b^-1*a^-1)^2*a^-1*b^-1*(b^-1*a^-1)^7*b^-6*a^-1*b^-2*(b^-2*((b^-1*a^-1)^7*\
    b^-6*a^-1)^2)^2*((b^-1*a^-1)^7*b^-6*a^-1)^3*a^-2*b^-1*(b^-1*a^-1)^2*(a^-1*b^-3)^2*(a^-1*\
    b^-1)^4*b^-1*a^-1*b^-2*a^-2*b^-2*(b^-3*a^-1)^2*b^-1*(b^-1*a^-1*b^4*(a^-1*b^-1)^7*b^-5*a^\
    -1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*(b^-1\
    *a^-1)^2*a^-3*b^-4*a^-2*b^-1*a^-1)^6*b^-1*a^-1*b^-1*((b^-1*a^-1)^7*(b^-6*a^-1*b^-1)^2*(a\
    ^-1*b^-1)^6*b^-5*a^-1)^2*(b^-1*a^-1)^7*b^-6*a^-3*(b^-2*a^-2*b^-1)^2*(b^-1*a^-1)^2*a^-1"),
   (2, "a^2*(a*b^2)^2*b^3*a^2*b*a*(b*a*b^2)^2*b*a*(a*b)^2*b*a^3*b^5*(b*a)^7*(b^3*a*b^5*(b*a)^7*b\
    ^2)^2*b^4*(b*a*b^5*(b*a)^7)^2*b^12*a^2*b*a^3*b^7*(a*b*a)^2*b^2*a*(a*b^5*(b*a)^7*b)^2*b*(\
    b^2*(b*a*b^5*(b*a)^7)^2)^2*b^3*a*b^5*(b*a)^7*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b\
    ^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^3*a^2*b*a^3*b^7*(a*b*a)^2*b^\
    2*a*(a*b^5*(b*a)^7*b)^2*b*(b^2*(b*a*b^5*(b*a)^7)^2)^2*b^3*a*b^5*(b*a)^7*b^-1*(a*b)^2*a^2\
    *b^4*a^3*b^2*a*b*a^-1*(b*a)^2*(b*a*b^2)^2*b*a*(a*b)^2*b*a^3*b^5*(b*a)^7*b^2*(b*a*b^5*(b*\
    a)^7)^3*b^4*(b*a*b^5*(b*a)^7)^5*b^8*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^\
    7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4*a^2*b*a^3*b^7*(a*b*a)^2*b^2*a*(a*b^5*(\
    b*a)^7*b)^2*b*(b^2*(b*a*b^5*(b*a)^7)^2)^2*b^3*a*b^5*(b*a)^7*(a*b)^2*a^2*b^4*a^3*(a*b)^2*\
    b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^2*((a*b)^2*a^2\
    *b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-\
    4)^6*a*(b^2*a*b)^2*b^4*a^2*b^2*a*b*(b*a)^4*(b^3*a)^2*(a*b)^2*b*a^2*(a*b^5*(b*a)^7*b)^2*a\
    *b^5*(b*a)^7*((b*a*b^5*(b*a)^7)^2*b^2)^2*b^3*a*b^5*(b*a)^7*b^2*(a^2*b*a^3*b^7*(a*b*a)^2*\
    b^2*a*(a*b^5*(b*a)^7*b)^2*b*(b^2*(b*a*b^5*(b*a)^7)^2)^2*b^3*a*b^5*(b*a)^7*((a*b)^2*a^2*b\
    ^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)\
    ^3)^2*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11\
    *a*b^5*(b*a)^7*b^-4)^2*b^-1",
    "b*(b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7\
    *b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2*a^-1)^4*b^4*(a^-1*b^-1\
    )^7*b^-5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1\
    *b^-3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2*((a^-1*b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-1\
    1*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^\
    2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2)^2*a^-1*((a^-1*b^-1)^7*b^-5*a^-1*b^-2*(b^-1*a^-1)^7*b^-6*\
    a^-1*b^-1)^2*(a^-1*b^-1)^7*b^-5*a^-1*b^-4*((b^-1*a^-1)^7*b^-6*a^-1)^2*a^-1*b^-2*(a^-1*b^\
    -1*a^-1)^2*b^-7*a^-3*b^-1*a^-1)^2*a^-1*b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^-1*b^-1)^7*\
    b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*\
    (a^-1*b^-1)^3*b^-6*((b^-1*a^-1)^7*b^-6*a^-1)^5*b^-4*((b^-1*a^-1)^7*b^-6*a^-1)^3*b^-2*(b^\
    -1*a^-1)^7*b^-6*a^-3*b^-1*(b^-1*a^-1)^2*(a^-1*b^-3)^2*(a^-1*b^-1)^3*a*b^-1*a^-1*b^-2*a^-\
    3*b^-4*a^-1*(a^-1*b^-1)^2*a^-1*b*(b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*\
    a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1\
    *b^-1)^2*a^-1)^2*b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3\
    *(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2*(a^-1*((\
    a^-1*b^-1)^7*b^-5*a^-1*b^-2*(b^-1*a^-1)^7*b^-6*a^-1*b^-1)^2*(a^-1*b^-1)^7*b^-5*a^-1*b^-4\
    *((b^-1*a^-1)^7*b^-6*a^-1)^2*a^-1*b^-2*(a^-1*b^-1*a^-1)^2*b^-7*a^-3*b^-1*a^-1)^3*a^-1*(b\
    ^-5*(b^-1*a^-1)^7*b^-6*a^-1*b^-1)^2*b^-3*((b^-1*a^-1)^7*b^-6*a^-1)^2*b^-6*(b^-1*a^-1)^7*\
    b^-4*(b^-2*a^-1)^2*b^-1*a^-4*b^-5*a^-2*b^-1*a^-1"),
   (2, "b^5*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^\
    -6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2*a^-1*b^4*(a^-1*b^-1)^7*b^\
    -5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*\
    (b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2*((a^-1*b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^\
    -1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3\
    *b^-4*a^-1*(a^-1*b^-1)^2)^3*a^-1*((a^-1*b^-1)^7*b^-5*a^-1*b^-2*(b^-1*a^-1)^7*b^-6*a^-1*b\
    ^-1)^2*(a^-1*b^-1)^7*b^-5*a^-1*b^-4*((b^-1*a^-1)^7*b^-6*a^-1)^2*a^-1*b^-2*(a^-1*b^-1*a^-\
    1)^2*b^-7*a^-3*b^-1*a^-1)^2*a^-1*b^-1*(b^-1*a^-1)^7*b^-6*a^-1*b^-2*(b^-2*((b^-1*a^-1)^7*\
    b^-6*a^-1)^2)^2*((b^-1*a^-1)^7*b^-6*a^-1)^3*a^-2*b^-1*(b^-1*a^-1)^2*(a^-1*b^-3)^2*(a^-1*\
    b^-1)^4*b^-1*a^-1*b^-2*a^-2*b^-2*(b^-3*a^-1)^2*b^-1*(b^-1*a^-1*b^4*(a^-1*b^-1)^7*b^-5*a^\
    -1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*(b^-1\
    *a^-1)^2*a^-3*b^-4*a^-2*b^-1*a^-1)^4*b^-1*(a^-1*((a^-1*b^-1)^7*b^-5*a^-1*b^-2*(b^-1*a^-1\
    )^7*b^-6*a^-1*b^-1)^2*(a^-1*b^-1)^7*b^-5*a^-1*b^-4*((b^-1*a^-1)^7*b^-6*a^-1)^2*a^-1*b^-2\
    *(a^-1*b^-1*a^-1)^2*b^-7*a^-3*b^-1*a^-1)^2*a^-1*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b^-4*((b^-1\
    *a^-1)^7*b^-6*a^-1)^5*b^-2*((b^-1*a^-1)^7*b^-6*a^-1)^2*a^-2*b^-1*(b^-1*a^-1)^2*(a^-1*b^-\
    3)^2*(a^-1*b^-1)^3*a^-2*b^-1*(b^-1*a^-1)^2*a^-1*(a^-2*b^-2)^2",
    "b^2*a*b^3*a^4*(b^2*a*b)^2*b^4*(b*a)^7*b^6*(b*a*b^5*(b*a)^7)^2*(b^3*a*b^5*(b*a)^7*b^2)^2*\
    b^2*(a^2*b*a^3*b^7*(a*b*a)^2*b^2*a*(a*b^5*(b*a)^7*b)^2*b*(b^2*(b*a*b^5*(b*a)^7)^2)^2*b^3\
    *a*b^5*(b*a)^7*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^\
    7)^2*b^11*a*b^5*(b*a)^7*b^-4)^2)^2*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7\
    *b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^4*b^-1"),
   (0, "b*(b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7\
    *b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2*a^-1)^9*(((a^-1*b^-1)^\
    7*b^-5*a^-1*b^-2*(b^-1*a^-1)^7*b^-6*a^-1*b^-1)^2*(a^-1*b^-1)^7*b^-5*a^-1*b^-4*((b^-1*a^-\
    1)^7*b^-6*a^-1)^2*a^-1*b^-2*(a^-1*b^-1*a^-1)^2*b^-7*a^-3*b^-1*a^-2*b^4*(a^-1*b^-1)^7*b^-\
    5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*(\
    b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2*a^-1)^2*b^-1*((b^-1*a^-1)^7*b^-6*a^-1)^2*b^-6*\
    ((b^-1*a^-1)^7*b^-6*a^-1)^2*((b^-1*a^-1)^7*b^-6*a^-1*b^-2)^2*a^-1*(a^-1*b^-2)^2*b^-7*a^-\
    1",
    "b^5*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^\
    -6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2*a^-1*b^4*(a^-1*b^-1)^7*b^\
    -5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*\
    (b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2*((a^-1*b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^\
    -1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3\
    *b^-4*a^-1*(a^-1*b^-1)^2)^3*a^-1*((a^-1*b^-1)^7*b^-5*a^-1*b^-2*(b^-1*a^-1)^7*b^-6*a^-1*b\
    ^-1)^2*(a^-1*b^-1)^7*b^-5*a^-1*b^-4*((b^-1*a^-1)^7*b^-6*a^-1)^2*a^-1*b^-2*(a^-1*b^-1*a^-\
    1)^2*b^-7*a^-3*b^-1*a^-1)^2*a^-1*b^-1*(b^-1*a^-1)^7*b^-6*a^-1*b^-2*(b^-2*((b^-1*a^-1)^7*\
    b^-6*a^-1)^2)^2*((b^-1*a^-1)^7*b^-6*a^-1)^3*a^-2*b^-1*(b^-1*a^-1)^2*(a^-1*b^-3)^2*(a^-1*\
    b^-1)^4*b^-1*a^-1*b^-2*a^-2*b^-2*(b^-3*a^-1)^2*b^-1*(b^-1*a^-1*b^4*(a^-1*b^-1)^7*b^-5*a^\
    -1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*(b^-1\
    *a^-1)^2*a^-3*b^-4*a^-2*b^-1*a^-1)^5*b^-1*((a^-1*b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^-\
    1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3*\
    b^-4*a^-1*(a^-1*b^-1)^2)^2*a^-1*((a^-1*b^-1)^7*b^-5*a^-1*b^-2*(b^-1*a^-1)^7*b^-6*a^-1*b^\
    -1)^2*(a^-1*b^-1)^7*b^-5*a^-1*b^-4*((b^-1*a^-1)^7*b^-6*a^-1)^2*a^-1*b^-2*(a^-1*b^-1*a^-1\
    )^2*b^-7*a^-3*b^-1*a^-1)^2*a^-1*b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^\
    -1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b\
    ^-1)^3*b^-6*((b^-1*a^-1)^7*b^-6*a^-1)^5*b^-4*((b^-1*a^-1)^7*b^-6*a^-1)^3*b^-2*(b^-1*a^-1\
    )^7*b^-6*a^-3*b^-1*(b^-1*a^-1)^2*(a^-1*b^-3)^2*(a^-1*b^-1)^3*a*b^-1*a^-1*b^-2*a^-3*b^-4*\
    a^-1*(a^-1*b^-1)^2*a^-1*b*(((a^-1*b^-1)^7*b^-5*a^-1*b^-2*(b^-1*a^-1)^7*b^-6*a^-1*b^-1)^2\
    *(a^-1*b^-1)^7*b^-5*a^-1*b^-4*((b^-1*a^-1)^7*b^-6*a^-1)^2*a^-1*b^-2*(a^-1*b^-1*a^-1)^2*b\
    ^-7*a^-3*b^-1*a^-2)^3*b^8*(a^-1*b^-1)^7*b^-5*a^-1*b^-4*(b^-2*(b^-1*a^-1)^7*b^-6*a^-1)^2*\
    ((b^-1*a^-1)^7*b^-6*a^-1)^2*b^-2*(b^-1*a^-1)^7*b^-6*a^-1*(b^-1*a^-1*b^-1)^2*b^-5"),
   (2, "b^4*(b^3*a)^2*a^2*(a*b)^4*b^2*a*b^3*a^2*b*(a*b^2*a)^2*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^\
    2*b*(b^6*a)^2*(b*a)^6*b^2*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a\
    *b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^2*a^2*b*a^3*b^7*(a*b*a)^2*b^2*a*(a*b^5*(b*a)^7*\
    b)^2*b*(b^2*(b*a*b^5*(b*a)^7)^2)^2*b^3*a*b^5*(b*a)^7*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*\
    b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^8*b^-1*(a*b)^2*a^2*b\
    ^4*a^3*b^2*a*b*a^-1*(b*a)^2*(b*a*b^2)^2*b*a*(a*b)^2*b*a^3*b^5*(b*a)^7*b^2*(b*a*b^5*(b*a)\
    ^7)^3*b^4*(b*a*b^5*(b*a)^7)^5*b^8*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*\
    b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4*a^2*b*a^3*b^7*(a*b*a)^2*b^2*a*(a*b^5*(b*\
    a)^7*b)^2*b*(b^2*(b*a*b^5*(b*a)^7)^2)^2*b^3*a*b^5*(b*a)^7*(a*b)^2*a^2*b^4*a^3*(a*b)^2*b^\
    3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^2*((a*b)^2*a^2*b\
    ^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)\
    ^6*b^-1",
    "b*(b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7\
    *b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2*a^-1)^8*((a^-1*b^-1)^7\
    *b^-5*a^-1*b^-2*(b^-1*a^-1)^7*b^-6*a^-1*b^-1)^2*(a^-1*b^-1)^7*b^-5*a^-1*b^-4*((b^-1*a^-1\
    )^7*b^-6*a^-1)^2*a^-1*b^-2*(a^-1*b^-1*a^-1)^2*b^-7*a^-3*b^-1*a^-1*(a^-1*b^4*(a^-1*b^-1)^\
    7*b^-5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b\
    ^-3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2)^2*a^-1*((a^-1*b^-1)^7*b^-5*a^-1*b^-2*(b^\
    -1*a^-1)^7*b^-6*a^-1*b^-1)^2*(a^-1*b^-1)^7*b^-5*a^-1*b^-4*((b^-1*a^-1)^7*b^-6*a^-1)^2*a^\
    -1*b^-2*(a^-1*b^-1*a^-1)^2*b^-7*a^-3*b^-1*a^-2*b^8*(a^-1*b^-1)^7*b^-5*a^-1*b^-2*(b^-2*(b\
    ^-1*a^-1)^7*b^-6*a^-1)^2*((b^-1*a^-1)^7*b^-6*a^-1)^2*b^-8*(b^-1*a^-1)^7*b^-5*(b^-1*a^-3)\
    ^2*b^-1*a^-1*b^-2*(b^-1*a^-2)^2*b^-2"),
   (2, "a^2*b^2*a^5*b^3*(b*a)^5*(b^3*a)^2*(a*b)^2*b*a*(a*b^4)^2*b*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^\
    4*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b\
    ^5*(b*a)^7*b^-4)^3*a^2*b*a^3*b^7*(a*b*a)^2*b^2*a*(a*b^5*(b*a)^7*b)^2*b*(b^2*(b*a*b^5*(b*\
    a)^7)^2)^2*b^3*a*b^5*(b*a)^7*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(\
    b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^4*b^-1*(a*b)^2*a^2*b^4*a^3*b^2*a*b*a^-1*(b*a\
    )^2*(b*a*b^2)^2*b*a*(a*b)^2*b*a^3*b^5*(b*a)^7*b^2*(b*a*b^5*(b*a)^7)^3*b^4*(b*a*b^5*(b*a)\
    ^7)^5*b^8*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*\
    b^11*a*b^5*(b*a)^7*b^-4*a^2*b*a^3*b^7*(a*b*a)^2*b^2*a*(a*b^5*(b*a)^7*b)^2*b*(b^2*(b*a*b^\
    5*(b*a)^7)^2)^2*b^3*a*b^5*(b*a)^7*(a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b\
    ^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^2*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-\
    1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^6*b^-1",
    "b*((a^-1*b^-1)^7*b^-5*a^-1*b^-2*(b^-1*a^-1)^7*b^-6*a^-1*b^-1)^2*(a^-1*b^-1)^7*b^-5*a^-1*\
    b^-4*((b^-1*a^-1)^7*b^-6*a^-1)^2*a^-1*b^-2*(a^-1*b^-1*a^-1)^2*b^-7*a^-3*b^-1*a^-1*(a^-1*\
    b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^\
    -6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2)^2*a^-1*((a^-1*b^-1)^7*b^\
    -5*a^-1*b^-2*(b^-1*a^-1)^7*b^-6*a^-1*b^-1)^2*(a^-1*b^-1)^7*b^-5*a^-1*b^-4*((b^-1*a^-1)^7\
    *b^-6*a^-1)^2*a^-1*b^-2*(a^-1*b^-1*a^-1)^2*b^-7*a^-3*b^-1*a^-2*b^4*(a^-1*b^-1)^7*b^-5*a^\
    -1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*(b^-1\
    *a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2*a^-1*b^4*(a^-1*b^-1)^5*a^-1*(b^-1*a^-1*b^-5)^2*(a^\
    -1*b^-1)^7*b^-5*a^-1*b^-4*((b^-1*a^-1)^7*b^-6*a^-1)^4*a^-2*b^-1*a^-5*b^-6"),
   (2, "b*(b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7\
    *b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2*a^-1)^3*b^4*(a^-1*b^-1\
    )^7*b^-5*a^-1*b^-11*((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1\
    *b^-3*(b^-1*a^-1)^2*a^-3*b^-4*a^-1*(a^-1*b^-1)^2*(a^-1*b^4*(a^-1*b^-1)^7*b^-5*a^-1*b^-11\
    *((a^-1*b^-1)^7*b^-5*a^-1*b^-1)^2*b^-3*(b^-1*a^-1)^7*b^-6*a^-1*b*a^-1*b^-3*(b^-1*a^-1)^2\
    *a^-3*b^-4*a^-1*(a^-1*b^-1)^2*a^-1*((a^-1*b^-1)^7*b^-5*a^-1*b^-2*(b^-1*a^-1)^7*b^-6*a^-1\
    *b^-1)^2*(a^-1*b^-1)^7*b^-5*a^-1*b^-4*((b^-1*a^-1)^7*b^-6*a^-1)^2*a^-1*b^-2*(a^-1*b^-1*a\
    ^-1)^2*b^-7*a^-3*b^-1*a^-1)^2*a^-1*b^-1*(b^-4*(b^-1*a^-1)^7*b^-6*a^-1)^3*(b^-1*a^-1)^7*b\
    ^-2*(b^-4*a^-1)^2*(a^-1*b^-2)^2*a^-1*b^-1*a^-2*b^-1",
    "b^2*a*b*(a*b^2*a)^2*b*a*(a*b)^4*b^2*a*b^3*a*(a*b)^2*b*a^2*b^5*(b*a*b^5*(b*a)^7)^2*b^15*a\
    *b^5*(b*a)^7*b^-4*(b^-4*(a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^\
    5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7)^3*b^-4*a^2*b*a^3*b^7*(a*b*a)^2*b^2*a*(a*b^5*(b*a)^7*b)^\
    2*b*(b^2*(b*a*b^5*(b*a)^7)^2)^2*b^3*a*b^5*(b*a)^7*(a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1\
    *a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-5*(a*b)^2*a^2*b^4*a^3*b^2*a\
    *b*a^-1*(b*a)^2*(b*a*b^2)^2*b*a*(a*b)^2*b*a^3*b^5*(b*a)^7*b^2*(b*a*b^5*(b*a)^7)^3*b^4*(b\
    *a*b^5*(b*a)^7)^5*b^8*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5\
    *(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4*a^2*b*a^3*b^7*(a*b*a)^2*b^2*a*(a*b^5*(b*a)^7*b)^2*b*\
    (b^2*(b*a*b^5*(b*a)^7)^2)^2*b^3*a*b^5*(b*a)^7*(a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b\
    ^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^2*((a*b)^2*a^2*b^4*a^3*(a*b)\
    ^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^6*b^-1"),
   (2, "a^3*b*(b*a^2)^2*a*(a*b)^6*b^2*a*b^3*a*(a*b)^2*b*a^2*(a*b^5*(b*a)^7*b)^3*b*((b^5*a*b)^2*(\
    a*b)^5*a)^2*b^5*(a*b^5*(b*a)^7*b^-4*(a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7\
    *b^4*(b*a*b^5*(b*a)^7)^2*b^11)^5*a*b^5*(b*a)^7*b^-4*a^2*b*a^3*b^7*(a*b*a)^2*b^2*a*(a*b^5\
    *(b*a)^7*b)^2*b*(b^2*(b*a*b^5*(b*a)^7)^2)^2*b^3*a*b^5*(b*a)^7*b^-1*(a*b)^2*a^2*b^4*a^3*b\
    ^2*a*b*a^-1*(b*a)^2*(b*a*b^2)^2*b*a*(a*b)^2*b*a^3*b^5*(b*a)^7*b^2*(b*a*b^5*(b*a)^7)^3*b^\
    4*(b*a*b^5*(b*a)^7)^5*b^8*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a\
    *b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4*a^2*b*a^3*b^7*(a*b*a)^2*b^2*a*(a*b^5*(b*a)^7*b)^\
    2*b*(b^2*(b*a*b^5*(b*a)^7)^2)^2*b^3*a*b^5*(b*a)^7*(a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1\
    *a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^2*((a*b)^2*a^2*b^4*a^3*(\
    a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^6*b^-1",
    "(b*a)^2*(a*(a*b)^2*b^2)^2*b*(b*a*b^5*(b*a)^7)^2*(b^3*a*b^5*(b*a)^7*b^2)^2*b*a*b^5*(b*a)^\
    7*b^10*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^1\
    1*a*b^5*(b*a)^7*b^-4)^2*(a^2*b*a^3*b^7*(a*b*a)^2*b^2*a*(a*b^5*(b*a)^7*b)^2*b*(b^2*(b*a*b\
    ^5*(b*a)^7)^2)^2*b^3*a*b^5*(b*a)^7)^2*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a\
    )^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^8*a*(b^2*a*b)^2*b^4*a^2*b^2*a*b*(b*\
    a)^4*(b^3*a)^2*(a*b)^2*b*a^2*(a*b^5*(b*a)^7*b)^2*a*b^5*(b*a)^7*((b*a*b^5*(b*a)^7)^2*b^2)\
    ^2*b^3*a*b^5*(b*a)^7*b^2*(a^2*b*a^3*b^7*(a*b*a)^2*b^2*a*(a*b^5*(b*a)^7*b)^2*b*(b^2*(b*a*\
    b^5*(b*a)^7)^2)^2*b^3*a*b^5*(b*a)^7*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3*a*b^-1*a*b^5*(b*a)^\
    7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^3)^2*((a*b)^2*a^2*b^4*a^3*(a*b)^2*b^3\
    *a*b^-1*a*b^5*(b*a)^7*b^4*(b*a*b^5*(b*a)^7)^2*b^11*a*b^5*(b*a)^7*b^-4)^2*b^-1")]

@[expose] def B0 (_ : Unit := ()) : Mat := mOfRows mRows

@[expose] def Da (_ : Unit := ()) : AD := adOfRows xRows c1 2

@[expose] def Db (_ : Unit := ()) : AD := adOfRows yRows c2 1

@[expose] def LA (_ : Unit := ()) : Array AD :=
  let B := B0 ()
  letterAD B (Da ()) (Db ()) ++ Array.ofFn (n := 12) fun i => adQ B i

@[expose] def LM (_ : Unit := ()) : Array Mat :=
  #[mOfRows xRows, mOfRows yRows, mOfRows xiRows, mOfRows yiRows]

@[expose] def sylWords (_ : Unit := ()) : Array WT :=
  let ws := sylGens.map parseWT
  (ws ++ ws.map WT.inv).toArray

@[expose] def sylMats (_ : Unit := ()) : Array Mat :=
  let L := LM ()
  (sylWords ()).map (matOf L)

@[expose] def sylInv (_ : Unit := ()) : Array Nat :=
  (List.range 14).toArray.map fun k => if k < 7 then k + 7 else k - 7

@[expose] def sylEnum (_ : Unit := ()) : Array Mat × Array Nat × Array Nat :=
  grpBFS (sylMats ()) 3000

@[expose] def sylEl (_ : Unit := ()) : Array Mat := (sylEnum ()).1

@[expose] def sylPar (_ : Unit := ()) : Array Nat := (sylEnum ()).2.1

@[expose] def sylGen (_ : Unit := ()) : Array Nat := (sylEnum ()).2.2

@[expose] def tMats (_ : Unit := ()) : Array Mat :=
  let L := LM ()
  sigW.map (matOf L)

@[expose] def sylRoots (_ : Unit := ()) : List Nat :=
  let L := LM ()
  let el := sylEl ()
  let m := keyMap el
  conjData.map fun (_, e, _) => lookupIdx m el.size (matOf L (parseWT e))

@[expose] def sylForest (_ : Unit := ()) : Array Nat × Array Nat × Array Nat :=
  conjBFS (sylMats ()) (sylInv ()) (sylEl ()) (sylRoots ())

@[expose] def sylInvOK (_ : Unit := ()) : Bool :=
  let gens := sylMats ()
  gens.size = 14 && (List.range 7).all fun k => meq (mmul gens[k]! gens[k + 7]!) mone &&
    meq (mmul gens[k + 7]! gens[k]!) mone

@[expose] def sylRootsOK (_ : Unit := ()) : Bool :=
  let L := LM ()
  let el := sylEl ()
  let T := tMats ()
  let roots := sylRoots ()
  T.size = 3 && roots.length = conjData.length &&
  (conjData.zip roots).all fun ((j, _, x), r) =>
    let X := matOf L (parseWT x)
    j < 3 && r < el.size && meq (mmul el[r]! X) (mmul X T[j]!)

@[expose] def sylCheck (_ : Unit := ()) : Bool :=
  let F := sylForest ()
  sylInvOK () && (sylEl ()).size = 2187 &&
  grpCheck (sylMats ()) (sylEl ()) (sylPar ()) (sylGen ()) &&
  conjCheck (sylMats ()) (sylEl ()) (sylRoots ()) F.1 F.2.1 F.2.2 && sylRootsOK ()

@[expose] def tD (k : Nat) : AD := adOf (B0 ()) (LA ()) sigW[k - 1]!

@[expose] def fT (k : Nat) : Mat := if k = 0 then mone else adMat (tD k)

@[expose] def fLam (k : Nat) : F3 := if k = 0 then 1 else (tD k).2

@[expose] def fGenWords (k : Nat) : Array WT :=
  if k = 0 then #[.gen 0, .gen 1]
  else (Array.ofFn (n := 12) fun i => WT.gen (4 + i.val)) ++
    ((match k with | 1 => cent1 | 2 => cent2 | _ => cent3).map parseWT).toArray

@[expose] def fRootV (k : Nat) : List (List Nat) :=
  match k with
  | 0 => [[0,0,0,0,0,0,0,0,0,0,0,0], [0,1,0,0,0,0,0,0,0,0,0,0], [1,0,0,0,0,0,0,0,0,0,0,0]]
  | 1 => [[0,0,0,0,0,0,0,0,0,0,0,0], [0,0,0,1,0,0,0,0,0,0,0,0], [1,0,0,0,0,0,0,0,0,0,0,0]]
  | 2 => [[0,0,0,0,0,0,0,0,0,0,0,0], [1,0,0,0,0,0,0,0,0,0,0,0]]
  | _ => [[0,0,0,0,0,0,0,0,0,0,0,0], [1,0,0,0,0,0,0,0,0,0,0,0], [0,0,0,0,0,1,0,0,0,0,0,0],
      [0,0,0,0,0,0,0,0,0,0,0,1], [1,1,0,0,0,0,0,0,0,0,0,0], [0,1,0,1,0,0,0,0,0,0,0,0]]

@[expose] def repD (k : Nat) (v : List Nat) : AD :=
  let B := B0 ()
  if k = 0 then nfD B (eOf v 0) else comp B (tD k) (nfD B (eOf v 0))

@[expose] def fibreOK (k : Nat) : Bool :=
  let B := B0 ()
  let L := LA ()
  let gd := (fGenWords k).map fun t => (adOf B L t, adOf B L (WT.inv t))
  fibreFull B (fT k) (fLam k) gd ((fRootV k).map (repD k))

end Timmesfeld.M3B
