module

public import Std.Data.HashMap

public section

namespace CFSG.PSL3Four.Native

abbrev Tab := Array Nat

@[expose] def comp (n : Nat) (p q : Tab) : Tab := Array.ofFn (n := n) fun i => p[q[i.val]!]!

@[expose] def idTab (n : Nat) : Tab := Array.ofFn (n := n) fun i => i.val

@[expose] def invTab (n : Nat) (p : Tab) : Tab := Id.run do
  let mut r : Tab := Array.replicate n 0
  for i in [0:n] do
    r := r.set! p[i]! i
  return r

@[expose] def conjTab (n : Nat) (g gi x : Tab) : Tab := comp n (comp n g x) gi

@[expose] def commTab (n : Nat) (x y xi yi : Tab) : Tab := comp n (comp n (comp n x y) xi) yi

@[expose] def allBelow (m : Nat) (f : Nat → Bool) : Bool := (List.range m).all f

@[expose] def anyBelow (m : Nat) (f : Nat → Bool) : Bool := (List.range m).any f

@[expose] def countBelow (m : Nat) (f : Nat → Bool) : Nat := ((List.range m).filter f).length

@[expose] def indexOf (T : Array Tab) : Std.HashMap Tab Nat := Id.run do
  let mut m : Std.HashMap Tab Nat := Std.HashMap.emptyWithCapacity T.size
  for k in [0:T.size] do
    m := m.insert T[k]! k
  return m

@[inline, expose] def posOf (idx : Std.HashMap Tab Nat) (T : Array Tab) (x : Tab) : Nat :=
  idx.getD x T.size

@[inline, expose] def found (idx : Std.HashMap Tab Nat) (T : Array Tab) (x : Tab) : Bool :=
  posOf idx T x < T.size && T[posOf idx T x]! == x

@[expose] def invsOK (n : Nat) (T inv : Array Tab) : Bool :=
  inv.size == T.size &&
    allBelow T.size fun k => (inv[k]!).size == n && comp n inv[k]! T[k]! == idTab n

structure Enum where
  tabs : Array Tab
  par : Array Nat
  lab : Array Nat
deriving Inhabited

@[expose] def bfs (step : Nat → Tab → Tab) (k : Nat) (root : Tab) (cap : Nat) : Enum := Id.run do
  let mut tabs : Array Tab := #[root]
  let mut par : Array Nat := #[0]
  let mut lab : Array Nat := #[0]
  let mut idx : Std.HashMap Tab Nat := (Std.HashMap.emptyWithCapacity cap).insert root 0
  for h in [0:cap] do
    if h < tabs.size then
      let t := tabs[h]!
      for j in [0:k] do
        let x := step j t
        if !idx.contains x then
          idx := idx.insert x tabs.size
          tabs := tabs.push x
          par := par.push h
          lab := lab.push j
    else break
  return ⟨tabs, par, lab⟩

@[expose] def treeOK (step : Nat → Tab → Tab) (k : Nat) (root : Tab) (E : Enum) : Bool :=
  let idx := indexOf E.tabs
  0 < E.tabs.size && E.tabs[0]! == root &&
    allBelow E.tabs.size fun i =>
      posOf idx E.tabs E.tabs[i]! == i &&
        allBelow k (fun j => found idx E.tabs (step j E.tabs[i]!)) &&
        (i == 0 || (E.par[i]! < i && E.lab[i]! < k &&
          E.tabs[i]! == step E.lab[i]! E.tabs[E.par[i]!]!))

@[expose] def leftStep (n : Nat) (gens : Array Tab) (j : Nat) (t : Tab) : Tab := comp n gens[j]! t

@[expose] def conjStep (n : Nat) (gens ginv : Array Tab) (j : Nat) (t : Tab) : Tab :=
  conjTab n gens[j]! ginv[j]! t

@[expose] def enumBFS (n : Nat) (gens : Array Tab) (cap : Nat) : Enum :=
  bfs (leftStep n gens) gens.size (idTab n) cap

@[expose] def enumOK (n : Nat) (gens : Array Tab) (E : Enum) : Bool :=
  treeOK (leftStep n gens) gens.size (idTab n) E

@[expose] def orbitBFS (n : Nat) (gens ginv : Array Tab) (x : Tab) (cap : Nat) : Enum :=
  bfs (conjStep n gens ginv) gens.size x cap

@[expose] def orbitOK (n : Nat) (gens ginv : Array Tab) (x : Tab) (E : Enum) : Bool :=
  invsOK n gens ginv && treeOK (conjStep n gens ginv) gens.size x E

@[expose] def centTabs (n : Nat) (T : Array Tab) (r : Tab) : Array Tab :=
  T.filter fun t => comp n t r == comp n r t

@[expose] def centralOK (n : Nat) (T gs : Array Tab) : Bool :=
  allBelow T.size fun k =>
    !(allBelow gs.size fun i => comp n T[k]! gs[i]! == comp n gs[i]! T[k]!) || T[k]! == idTab n

@[expose] def coverOK (n : Nat) (T : Array Tab) (O : Array (Array Tab)) : Bool :=
  let idxs := O.map indexOf
  allBelow T.size fun k =>
    T[k]! == idTab n || !(comp n T[k]! T[k]! == idTab n) ||
      anyBelow O.size fun i => found idxs[i]! O[i]! T[k]!

@[expose] def notInOK (T : Array Tab) (x : Tab) : Bool := allBelow T.size fun k => !(T[k]! == x)

@[expose] def normalOK (n : Nat) (T gens ginv gs : Array Tab) : Bool :=
  let idx := indexOf T
  invsOK n gens ginv &&
    allBelow gens.size fun j => allBelow gs.size fun i =>
      found idx T (conjTab n gens[j]! ginv[j]! gs[i]!) &&
        found idx T (conjTab n ginv[j]! gens[j]! gs[i]!)

structure ClassData where
  lab : Array Nat
  reps : Array Nat
  wit : Array Nat
deriving Inhabited

@[expose] def classData (n : Nat) (T : Array Tab) (target : Array Nat) : ClassData := Id.run do
  let m := T.size
  let idx := indexOf T
  let inv := T.map (invTab n)
  let mut lab : Array Nat := Array.replicate m m
  let mut wit : Array Nat := Array.replicate m 0
  let mut reps : Array Nat := Array.replicate target.size 0
  let mut used : Array Bool := Array.replicate target.size false
  for k in [0:m] do
    if lab[k]! == m then
      let mut cls : Array (Nat × Nat) := #[]
      let mut seen : Std.HashMap Nat Unit := {}
      for a in [0:m] do
        let p := posOf idx T (conjTab n T[a]! inv[a]! T[k]!)
        if p < m && !seen.contains p then
          seen := seen.insert p ()
          cls := cls.push (p, a)
      let mut l := target.size
      for i in [0:target.size] do
        if l == target.size && !used[i]! && target[i]! == cls.size then
          l := i
      if l < target.size then
        used := used.set! l true
        reps := reps.set! l k
      for (p, a) in cls do
        lab := lab.set! p l
        wit := wit.set! p a
  return ⟨lab, reps, wit⟩

@[expose] def classOK (n : Nat) (T inv : Array Tab) (C : ClassData) (sizes : Array Nat) : Bool :=
  let m := T.size
  let idx := indexOf T
  invsOK n T inv &&
    (allBelow m fun k => posOf idx T T[k]! == k) &&
    (allBelow m fun k => allBelow m fun a =>
      let y := conjTab n T[a]! inv[a]! T[k]!
      found idx T y && C.lab[posOf idx T y]! == C.lab[k]!) &&
    C.reps.size == sizes.size &&
    (allBelow sizes.size fun l => C.reps[l]! < m && C.lab[C.reps[l]!]! == l) &&
    (allBelow m fun k => C.lab[k]! < sizes.size && C.wit[k]! < m &&
      conjTab n T[C.wit[k]!]! inv[C.wit[k]!]! T[C.reps[C.lab[k]!]!]! == T[k]!) &&
    (allBelow sizes.size fun l => countBelow m (fun k => C.lab[k]! == l) == sizes[l]!) &&
    0 < m && T[0]! == idTab n && C.lab[0]! == 0

@[expose] def derivedData (n : Nat) (T inv : Array Tab) :
    Array Tab × Array (Nat × Nat × Nat × Nat) := Id.run do
  let m := T.size
  let mut cs : Array Tab := #[]
  let mut cw : Array (Nat × Nat) := #[]
  let mut cidx : Std.HashMap Tab Nat := {}
  for a in [0:m] do
    for b in [0:m] do
      let x := commTab n T[a]! T[b]! inv[a]! inv[b]!
      if !cidx.contains x then
        cidx := cidx.insert x cs.size
        cs := cs.push x
        cw := cw.push (a, b)
  let mut D : Array Tab := #[]
  let mut W : Array (Nat × Nat × Nat × Nat) := #[]
  let mut didx : Std.HashMap Tab Nat := {}
  for u in [0:cs.size] do
    for v in [0:cs.size] do
      let x := comp n cs[u]! cs[v]!
      if !didx.contains x then
        didx := didx.insert x D.size
        D := D.push x
        W := W.push (cw[u]!.1, cw[u]!.2, cw[v]!.1, cw[v]!.2)
  return (D, W)

@[expose] def derivedOK (n : Nat) (T inv D : Array Tab) (W : Array (Nat × Nat × Nat × Nat)) :
    Bool :=
  let m := T.size
  let idx := indexOf D
  invsOK n T inv &&
    (allBelow D.size fun a => posOf idx D D[a]! == a) &&
    found idx D (idTab n) &&
    (allBelow D.size fun a => allBelow D.size fun b => found idx D (comp n D[a]! D[b]!)) &&
    (allBelow D.size fun a =>
      found idx D (invTab n D[a]!) && comp n (invTab n D[a]!) D[a]! == idTab n) &&
    (allBelow m fun a => allBelow m fun b => found idx D (commTab n T[a]! T[b]! inv[a]! inv[b]!)) &&
    W.size == D.size &&
    allBelow D.size fun a =>
      W[a]!.1 < m && W[a]!.2.1 < m && W[a]!.2.2.1 < m && W[a]!.2.2.2 < m &&
        D[a]! == comp n (commTab n T[W[a]!.1]! T[W[a]!.2.1]! inv[W[a]!.1]! inv[W[a]!.2.1]!)
          (commTab n T[W[a]!.2.2.1]! T[W[a]!.2.2.2]! inv[W[a]!.2.2.1]! inv[W[a]!.2.2.2]!)

end CFSG.PSL3Four.Native
