module

public import Certificates.Data.CFSGNative.Schreier.Enum3
public import Certificates.Data.CFSGNative.Schreier.SetOrbit
public import Certificates.Data.CFSGNative.Schreier.Refine
public import Std.Data.HashMap

public section

namespace CFSG.Sporadic.FischerOddCore.Native

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

@[expose] def isInvArr (m : Nat) (g : Array Nat) : Bool :=
  !(eqA m g (idA m)) && eqA m (compA m g g) (idA m)

@[expose] def conjArr (m : Nat) (g gi a : Array Nat) : Array Nat :=
  compA m g (compA m a gi)

@[expose] def powA (m : Nat) (g : Array Nat) : Nat → Array Nat
  | 0 => idA m
  | k + 1 => compA m g (powA m g k)

@[expose] def resPt (L : Array Level) (q qi v D pos : Array Nat) (x : Nat × Nat × Nat) (e : Bool)
    (i : Nat) : Nat :=
  pos[q[tr3 L x.1 x.2.1 x.2.2 qi[if e then v[D[i]!]! else D[i]!]!]!]!

@[expose] def extSize (L : Array Level) : Nat :=
  2 * L[0]!.pts.size * L[1]!.pts.size * L[2]!.pts.size

@[expose] def unidxS (L : Array Level) (I : Nat) : (Nat × Nat × Nat) × Bool :=
  let j := I / 2
  let s₂ := L[2]!.pts.size
  let s₁ := L[1]!.pts.size
  ((j / s₂ / s₁, j / s₂ % s₁, j % s₂), I % 2 == 1)

@[expose] def resIdx (m : Nat) (L : Array Level) (q qi v D pos : Array Nat) (I : Nat) :
    Array Nat :=
  let c := unidxS L I
  Array.ofFn (n := m) fun i => resPt L q qi v D pos c.1 c.2 i.val

structure LabelCert where
  lab : Array Nat
  par : Array Nat
  gen : Array Nat
  dep : Array Nat
  nb : Array Nat
deriving Inhabited

@[expose] def labelSearch (m sz : Nat) (res : Nat → Array Nat) (steps stepsInv : Array (Array Nat))
    (roots : Array Nat) : LabelCert := Id.run do
  let r := roots.size
  let ns := steps.size
  let mut inv : Std.HashMap (Array Nat) Nat := {}
  let mut invs : Array Nat := #[]
  for I in [0:sz] do
    let a := res I
    if isInvArr m a then
      inv := inv.insert a I
      invs := invs.push I
  let mut lab : Array Nat := Array.replicate sz r
  let mut par : Array Nat := Array.replicate sz 0
  let mut gen : Array Nat := Array.replicate sz 0
  let mut dep : Array Nat := Array.replicate sz 0
  for j in [0:r] do
    let I0 := roots[j]!
    if I0 < sz && lab[I0]! == r then
      lab := lab.set! I0 j
      let mut queue : Array Nat := #[I0]
      let mut head := 0
      for _ in [0:sz] do
        if head < queue.size then
          let I := queue[head]!
          head := head + 1
          let a := res I
          for s in [0:ns] do
            let y := conjArr m steps[s]! stepsInv[s]! a
            match inv[y]? with
            | some J =>
              if lab[J]! == r then
                lab := lab.set! J j
                par := par.set! J I
                gen := gen.set! J s
                dep := dep.set! J (dep[I]! + 1)
                queue := queue.push J
            | none => pure ()
        else
          break
  let mut nb : Array Nat := Array.replicate (sz * ns) 0
  for I in invs do
    let a := res I
    for s in [0:ns] do
      nb := nb.set! (I * ns + s) (inv.getD (conjArr m steps[s]! stepsInv[s]! a) sz)
  return ⟨lab, par, gen, dep, nb⟩

@[expose] def labelOKAt (m sz : Nat) (res : Nat → Array Nat) (steps stepsInv : Array (Array Nat))
    (roots : Array Nat) (C : LabelCert) (I : Nat) : Bool :=
  let r := roots.size
  let a := res I
  let l := C.lab[I]!
  if isInvArr m a then
    decide (l < r) &&
      (if C.dep[I]! == 0 then I == roots[l]!
      else
        let J := C.par[I]!
        let s := C.gen[I]!
        decide (J < sz) && decide (C.dep[J]! < C.dep[I]!) && C.lab[J]! == l &&
          decide (s < steps.size) && eqA m a (conjArr m steps[s]! stepsInv[s]! (res J))) &&
      allLt steps.size (fun s =>
        let J := C.nb[I * steps.size + s]!
        decide (J < sz) && C.lab[J]! == l &&
          eqA m (res J) (conjArr m steps[s]! stepsInv[s]! a))
  else l == r

@[expose] def labelOK (m sz : Nat) (res : Nat → Array Nat) (steps stepsInv : Array (Array Nat))
    (roots : Array Nat) (C : LabelCert) (chunks : Nat) : Bool :=
  parLt sz chunks (labelOKAt m sz res steps stepsInv roots C)

@[expose] def labelSearchRes (m sz : Nat) (L : Array Level) (q qi v D pos : Array Nat)
    (steps stepsInv : Array (Array Nat)) (roots : Array Nat) : LabelCert :=
  labelSearch m sz (resIdx m L q qi v D pos) steps stepsInv roots

@[expose] def labelOKRes (m sz : Nat) (L : Array Level) (q qi v D pos : Array Nat)
    (steps stepsInv : Array (Array Nat)) (roots : Array Nat) (C : LabelCert) (chunks : Nat) :
    Bool :=
  labelOK m sz (resIdx m L q qi v D pos) steps stepsInv roots C chunks

@[expose] def labelledCount (lab : Array Nat) (sz r : Nat) : Nat :=
  (List.range sz).countP fun I => decide (lab[I]! < r)

@[expose] def labCount (lab : Array Nat) (sz j : Nat) : Nat :=
  (List.range sz).countP fun I => lab[I]! == j

@[expose] def cmod (_ : Unit := ()) : Nat := 2147483629

@[expose] def hcol (x : Nat) : Nat :=
  let y := (x % cmod * 1000003 + 12345) % cmod
  let y := (y * y + 7919) % cmod
  (y * y + 104729) % cmod

@[expose] def nbrSum (nbr : Array (List Nat)) (c : Array Nat) (v : Nat) : Nat :=
  ((nbr[v]!).map fun w => hcol c[w]!).sum

@[expose] def stepT (n : Nat) (nbr : Array (List Nat)) (t c : Array Nat) : Array Nat :=
  Array.ofFn (n := n) fun v =>
    ((c[v.val]! % cmod * 1000003 + c[t[v.val]!]! % cmod) % cmod * 1000003 +
      nbrSum nbr c v.val) % cmod

@[expose] def refineT (n : Nat) (nbr : Array (List Nat)) (t c : Array Nat) : Nat → Array Nat
  | 0 => c
  | k + 1 => stepT n nbr t (refineT n nbr t c k)

@[expose] def initT (n : Nat) (t : Array Nat) (pre : List Nat) : Array Nat :=
  Array.ofFn (n := n) fun v =>
    2 * (match pre.idxOf? v.val with
      | some j => j + 1
      | none => 0) + (if t[v.val]! == v.val then 1 else 0)

@[expose] def colourT (n : Nat) (nbr : Array (List Nat)) (t : Array Nat) (pre : List Nat)
    (k : Nat) : Array Nat :=
  refineT n nbr t (initT n t pre) k

@[expose] def cellCount (n : Nat) (c : Array Nat) (col : Nat) : Nat :=
  (List.range n).countP fun w => c[w]! == col

@[expose] def colInj (n : Nat) (c : Array Nat) : Bool :=
  let l := ((List.range n).map fun w => c[w]!).mergeSort fun a b => decide (a ≤ b)
  strictIncr l

structure SNode where
  pre : List Nat
  kids : List (Nat × Nat)
  pool : List Nat
  out : Nat
  acc : Nat
deriving Inhabited

@[expose] def orbitCert (n : Nat) (gens : Array (Array Nat)) (reps : List Nat) :
    Array (Nat × Nat × Nat × Nat) := Id.run do
  let mut oc : Array (Nat × Nat × Nat × Nat) := Array.replicate n (0, 0, 0, 0)
  let mut k := 0
  for r in reps do
    k := k + 1
    if r < n && oc[r]!.1 == 0 then
      oc := oc.set! r (k, r, 0, 1)
      let mut queue : Array Nat := #[r]
      let mut head := 0
      for _ in [0:n] do
        if head < queue.size then
          let x := queue[head]!
          head := head + 1
          for g in [0:gens.size] do
            let y := (gens[g]!)[x]!
            if y < n && oc[y]!.1 == 0 then
              oc := oc.set! y (k, x, g, oc[x]!.2.2.2 + 1)
              queue := queue.push y
        else
          break
  return oc

@[expose] def orbitRecOK (gens : Array (Array Nat)) (reps : List Nat)
    (oc : Array (Nat × Nat × Nat × Nat)) (w : Nat) : Bool :=
  let e := oc[w]!
  let k := e.1
  let p := e.2.1
  let g := e.2.2.1
  let d := e.2.2.2
  k == 0 || (decide (k ≤ reps.length) && decide (0 < d) &&
    (if d == 1 then w == reps.getD (k - 1) 0
    else oc[p]!.1 == k && decide (oc[p]!.2.2.2 < d) && decide (g < gens.size) &&
      (gens[g]!)[p]! == w))

@[expose] def nodeGens (pool : Array (Array Nat)) (N : SNode) : Array (Array Nat) :=
  (N.pool.map fun j => pool[j]!).toArray

@[expose] def branchOK (n : Nat) (pool : Array (Array Nat)) (nodes : Array SNode) (c : Array Nat)
    (col : Nat) (N : SNode) : Bool :=
  let gens := nodeGens pool N
  let reps := N.kids.map Prod.fst
  let oc := orbitCert n gens reps
  N.out == 0 && oc.size == n &&
    N.pool.all (fun j => decide (j < pool.size)) &&
    gens.all (fun g => N.pre.all fun x => g[x]! == x) &&
    N.kids.all (fun rk => decide (rk.2 < nodes.size) && (nodes[rk.2]!).pre == N.pre ++ [rk.1]) &&
    allLt n (orbitRecOK gens reps oc) &&
    allLt n (fun w => c[w]! != col || oc[w]!.1 != 0)

@[expose] def colMatch (n : Nat) (c src : Array Nat) : Array Nat := Id.run do
  let mut mp : Std.HashMap Nat Nat := {}
  for w in [0:n] do
    mp := mp.insert c[w]! w
  return Array.ofFn (n := n) fun v => mp.getD src[v.val]! n

@[expose] def violAt (nbr : Array (List Nat)) (t A : Array Nat) (x : Nat) : Bool :=
  imgSorted A nbr[x]! != nbr[A[x]!]! || A[t[x]!]! != t[A[x]!]!

@[expose] def violSearch (n : Nat) (nbr : Array (List Nat)) (t A : Array Nat) : Nat :=
  ((List.range n).find? (violAt nbr t A)).getD n

@[expose] def missSearch (n : Nat) (A : Array Nat) : Nat :=
  ((List.range n).find? fun v => decide (n ≤ A[v]!)).getD n

@[expose] def leafOK (n : Nat) (nbr : Array (List Nat)) (t : Array Nat) (acc : Array (Array Nat))
    (c src : Array Nat) (N : SNode) : Bool :=
  let A := colMatch n c src
  let full := allLt n fun v => decide (A[v]! < n) && c[A[v]!]! == src[v]!
  if N.out == 1 then full && decide (N.acc < acc.size) && eqA n A acc[N.acc]!
  else if N.out == 2 then
    if full then
      let x := violSearch n nbr t A
      decide (x < n) && violAt nbr t A x
    else
      let v := missSearch n A
      decide (v < n) && allLt n fun w => c[w]! != src[v]!
  else false

@[expose] def searchOK (n : Nat) (nbr : Array (List Nat)) (t : Array Nat) (base : List Nat)
    (pool : Array (Array Nat)) (nodes : Array SNode) (acc : Array (Array Nat)) (K chunks : Nat) :
    Bool :=
  let srcs := ((List.range (base.length + 1)).map fun d => colourT n nbr t (base.take d) K).toArray
  let src := srcs[base.length]!
  decide (0 < nodes.size) && (nodes[0]!).pre == [] && colInj n src &&
    parLt nodes.size chunks fun i =>
      let N := nodes[i]!
      let d := N.pre.length
      let c := colourT n nbr t N.pre K
      if d < base.length then branchOK n pool nodes c (srcs[d]!)[base.getD d 0]! N
      else leafOK n nbr t acc c src N

@[expose] def boundsOK (n : Nat) (nbr : Array (List Nat)) (t : Array Nat) (pts bounds : List Nat)
    (K : Nat) : Bool :=
  pts.length == bounds.length &&
    allLt pts.length (fun s =>
      let c := colourT n nbr t (pts.take s) K
      cellCount n c c[pts.getD s 0]! == bounds.getD s 0) &&
    colInj n (colourT n nbr t pts K)

@[expose] def closureSearch (n : Nat) (gens : Array (Array Nat)) (bound : Nat) :
    Array (Array Nat) × Array Nat × Array Nat × Array Nat := Id.run do
  let one := idA n
  let mut E : Array (Array Nat) := #[one]
  let mut par : Array Nat := #[0]
  let mut gen : Array Nat := #[0]
  let mut idx : Std.HashMap (Array Nat) Nat := ({} : Std.HashMap (Array Nat) Nat).insert one 0
  let mut head := 0
  for _ in [0:bound] do
    if head < E.size then
      let x := E[head]!
      for k in [0:gens.size] do
        let y := compA n gens[k]! x
        if !idx.contains y then
          idx := idx.insert y E.size
          E := E.push y
          par := par.push head
          gen := gen.push k
      head := head + 1
    else
      break
  let gs := gens.size
  let mut nxt : Array Nat := Array.replicate (E.size * gs) E.size
  for i in [0:E.size] do
    for k in [0:gs] do
      nxt := nxt.set! (i * gs + k) (idx.getD (compA n gens[k]! E[i]!) E.size)
  return (E, par, gen, nxt)

@[expose] def closureOK (n : Nat) (gens E : Array (Array Nat)) (par gen nxt : Array Nat) : Bool :=
  let gs := gens.size
  decide (0 < E.size) && eqA n E[0]! (idA n) &&
    allLt E.size (fun i => i == 0 || (decide (par[i]! < i) && decide (gen[i]! < gs) &&
      eqA n E[i]! (compA n gens[gen[i]!]! E[par[i]!]!))) &&
    allLt E.size (fun i => allLt gs fun k =>
      decide (nxt[i * gs + k]! < E.size) && eqA n E[nxt[i * gs + k]!]! (compA n gens[k]! E[i]!))

@[expose] def keyAt (n : Nat) (b : List Nat) (g : Array Nat) : Nat :=
  b.foldr (fun x k => g[x]! + n * k) 0

@[expose] def keysOK (n : Nat) (b : List Nat) (E : Array (Array Nat)) : Bool :=
  let l := (E.toList.map (keyAt n b)).mergeSort fun a c => decide (a ≤ c)
  strictIncr l

@[expose] def isOrdP (n p : Nat) (g : Array Nat) : Bool :=
  !(eqA n g (idA n)) && eqA n (powA n g p) (idA n)

@[expose] def coverSearch (n p : Nat) (E xs : Array (Array Nat)) : Array (Nat × Nat × Nat) :=
  Id.run do
  let mut idx : Std.HashMap (Array Nat) Nat := {}
  for i in [0:E.size] do
    idx := idx.insert E[i]! i
  let mut cov : Array (Nat × Nat × Nat) := Array.replicate E.size (xs.size, 0, 0)
  for w in [0:xs.size] do
    for s in [0:E.size] do
      let si := invCand n E[s]!
      for j in [1:p] do
        let y := conjArr n E[s]! si (powA n xs[w]! j)
        match idx[y]? with
        | some i => if cov[i]!.1 == xs.size then cov := cov.set! i (w, s, j)
        | none => pure ()
  return cov

@[expose] def coverOK (n p : Nat) (E xs : Array (Array Nat)) (cov : Array (Nat × Nat × Nat)) :
    Bool :=
  allLt E.size fun i =>
    !(isOrdP n p E[i]!) ||
      (let e := cov[i]!
      decide (e.1 < xs.size) && decide (e.2.1 < E.size) && decide (0 < e.2.2) &&
        decide (e.2.2 < p) &&
        eqA n (compA n E[e.2.1]! (powA n xs[e.1]! e.2.2)) (compA n E[i]! E[e.2.1]!))

@[expose] def ordPCount (n p : Nat) (E : Array (Array Nat)) : Nat :=
  E.toList.countP (isOrdP n p)

end CFSG.Sporadic.FischerOddCore.Native
