module

public import Certificates.Data.CFSGNative.SCATWreathData

public section

namespace CFSG.SCATWreath

@[expose] def mCol (m j : Nat) : Nat := (m >>> (6 * j)) &&& 63

@[expose] def mSel (v j c : Nat) : Nat := if v.testBit j then c else 0

@[expose] def mAct (m v : Nat) : Nat :=
  mSel v 0 (mCol m 0) ^^^ mSel v 1 (mCol m 1) ^^^ mSel v 2 (mCol m 2) ^^^ mSel v 3 (mCol m 3) ^^^
    mSel v 4 (mCol m 4) ^^^ mSel v 5 (mCol m 5)

@[expose] def mPack (c₀ c₁ c₂ c₃ c₄ c₅ : Nat) : Nat :=
  c₀ + 64 * (c₁ + 64 * (c₂ + 64 * (c₃ + 64 * (c₄ + 64 * c₅))))

@[expose] def mMul (a b : Nat) : Nat :=
  mPack (mAct a (mCol b 0)) (mAct a (mCol b 1)) (mAct a (mCol b 2)) (mAct a (mCol b 3))
    (mAct a (mCol b 4)) (mAct a (mCol b 5))

@[expose] def smulTab (L : List Nat) : Array Nat :=
  let A := L.toArray
  Array.ofFn (n := 128 * 128) fun ij => L.idxOf (mMul A[ij.1 / 128]! A[ij.1 % 128]!)

@[expose] def actTab (L : List Nat) : Array Nat :=
  let A := L.toArray
  Array.ofFn (n := 128 * 64) fun iv => mAct A[iv.1 / 64]! (iv.1 % 64)

@[expose] def wMul (sm ac : Array Nat) (a b : Nat) : Nat :=
  64 * sm[a / 64 * 128 + b / 64]! + (a % 64 ^^^ ac[a / 64 * 64 + b % 64]!)

@[expose] def extMul (mul : Nat → Nat → Nat) (F : Array Nat) (g : Nat) (a b : Nat) : Nat :=
  if a % 2 = 0 then 2 * mul (a / 2) (b / 2) + b % 2
  else if b % 2 = 0 then 2 * mul (a / 2) F[b / 2]! + 1
  else 2 * mul (mul (a / 2) F[b / 2]!) g

@[expose] def pw (mul : Nat → Nat → Nat) (c : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => mul c (pw mul c k)

@[expose] def ordLoop (mul : Nat → Nat → Nat) (c : Nat) : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | f + 1, x, k => if x == 0 then k else ordLoop mul c f (mul c x) (k + 1)

@[expose] def ordc (mul : Nat → Nat → Nat) (c : Nat) : Nat := ordLoop mul c 64 (mul c 0) 1

@[expose] def ordTab (n : Nat) (mul : Nat → Nat → Nat) : Array Nat :=
  Array.ofFn (n := n) fun c => ordc mul c.1

@[expose] def invTab (n : Nat) (mul : Nat → Nat → Nat) (ord : Array Nat) : Array Nat :=
  Array.ofFn (n := n) fun c => pw mul c.1 (ord[c.1]! - 1)

@[expose] def invOK (n : Nat) (mul : Nat → Nat → Nat) (inv : Array Nat) : Bool :=
  (List.range n).all fun c => inv[c]! < n && mul c inv[c]! == 0

@[expose] def bfsTree (n : Nat) (mul : Nat → Nat → Nat) (gens : Array Nat) :
    Array Nat × Array Nat × Array Nat × Array Nat := Id.run do
  let mut seen := (Array.replicate n false).set! 0 true
  let mut par := Array.replicate n 0
  let mut gi := Array.replicate n 0
  let mut dep := Array.replicate n 0
  let mut q : Array Nat := #[0]
  let mut h := 0
  while h < q.size do
    let x := q[h]!
    h := h + 1
    for i in [0:gens.size] do
      let y := mul gens[i]! x
      if !seen[y]! then
        seen := seen.set! y true
        par := par.set! y x
        gi := gi.set! y i
        dep := dep.set! y (dep[x]! + 1)
        q := q.push y
  return (par, gi, dep, q)

@[expose] def treeOK (n : Nat) (mul : Nat → Nat → Nat) (gens par gi dep : Array Nat) : Bool :=
  gens.all (· < n) && (List.range n).all fun c =>
    c == 0 || (par[c]! < n && gi[c]! < gens.size && dep[par[c]!]! < dep[c]! && dep[c]! < n &&
      mul gens[gi[c]!]! par[c]! == c)

@[expose] def buildF (n : Nat) (mul : Nat → Nat → Nat) (par gi order imgs : Array Nat) :
    Array Nat := Id.run do
  let mut F := Array.replicate n 0
  for c in order do
    if c != 0 then F := F.set! c (mul imgs[gi[c]!]! F[par[c]!]!)
  return F

@[expose] def recOK (n : Nat) (mul : Nat → Nat → Nat) (par gi imgs F : Array Nat) : Bool :=
  F[0]! == 0 && (List.range n).all fun c => c == 0 || F[c]! == mul imgs[gi[c]!]! F[par[c]!]!

@[expose] def edgeOK (n : Nat) (mul : Nat → Nat → Nat) (gens imgs F : Array Nat) : Bool :=
  (List.range n).all fun c =>
    (List.range gens.size).all fun i => F[mul gens[i]! c]! == mul imgs[i]! F[c]!

@[expose] def fpath (mul : Nat → Nat → Nat) (par gi imgs : Array Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | f + 1, c => if c == 0 then 0 else mul imgs[gi[c]!]! (fpath mul par gi imgs f par[c]!)

@[expose] def labelBFS (n : Nat) (mul : Nat → Nat → Nat) (gens ginv : Array Nat)
    (dom : List Nat) : Array Nat × Array Nat × Array Nat := Id.run do
  let mut lab := Array.replicate n n
  let mut wit := Array.replicate n 0
  let mut reps : Array Nat := #[]
  for c in dom do
    if lab[c]! == n then
      let l := reps.size
      reps := reps.push c
      lab := lab.set! c l
      wit := wit.set! c 0
      let mut q : Array Nat := #[c]
      let mut h := 0
      while h < q.size do
        let x := q[h]!
        h := h + 1
        let wx := wit[x]!
        for i in [0:gens.size] do
          let y := mul (mul gens[i]! x) ginv[i]!
          if lab[y]! == n then
            lab := lab.set! y l
            wit := wit.set! y (mul gens[i]! wx)
            q := q.push y
  return (lab, reps, wit)

@[expose] def labOK (n : Nat) (mul : Nat → Nat → Nat) (gens ginv lab reps wit : Array Nat)
    (dom : List Nat) : Bool :=
  (List.range gens.size).all (fun i => gens[i]! < n && ginv[i]! < n &&
    mul gens[i]! ginv[i]! == 0) && reps.all (· < n) &&
  dom.all fun c => lab[c]! < reps.size && wit[c]! < n &&
    mul c wit[c]! == mul wit[c]! reps[lab[c]!]! &&
    (List.range gens.size).all fun i => lab[mul (mul gens[i]! c) ginv[i]!]! == lab[c]!

@[expose] def histo (m : Nat) (f : Array Nat) (dom : List Nat) : Array Nat :=
  dom.foldl (fun acc c => acc.modify f[c]! (· + 1)) (Array.replicate m 0)

@[expose] def invols (n : Nat) (mul : Nat → Nat → Nat) : List Nat :=
  (List.range n).filter fun c => c != 0 && mul c c == 0

@[expose] def cntC (mul : Nat → Nat → Nat) (dom : List Nat) (r : Nat) : Nat :=
  (dom.filter fun c => mul r c == mul c r).length

@[expose] def charOf (n : Nat) (par gi order : Array Nat) (v : Array Bool) :
    Array Bool := Id.run do
  let mut X := Array.replicate n false
  for c in order do
    if c != 0 then X := X.set! c (X[par[c]!]! != v[gi[c]!]!)
  return X

@[expose] def charOK (n : Nat) (mul : Nat → Nat → Nat) (gens : Array Nat) (v X : Array Bool) :
    Bool :=
  !X[0]! && (List.range n).all fun c =>
    (List.range gens.size).all fun i => X[mul gens[i]! c]! == (X[c]! != v[i]!)

end CFSG.SCATWreath
