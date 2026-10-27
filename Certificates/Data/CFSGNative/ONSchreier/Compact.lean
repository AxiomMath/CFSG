module

public import Init

public section

namespace CFSG.ONSchreier.Native

set_option compiler.extract_closed false

@[inline, expose] def allBelowN (n : Nat) (p : Nat → Bool) : Bool := Nat.all n fun i _ => p i

@[expose] def parBelow (n chunks : Nat) (p : Nat → Bool) : Bool :=
  let sz := n / chunks + 1
  ((List.range chunks).map fun c => Task.spawn fun _ =>
    allBelowN sz fun k => !(decide (c * sz + k < n)) || p (c * sz + k)).all Task.get

@[expose] def pcomp (n : Nat) (t u : Array Nat) : Array Nat :=
  Array.ofFn (n := n) fun i => t[u[i.val]!]!

@[expose] def pid (n : Nat) : Array Nat := Array.ofFn (n := n) fun i => i.val

@[expose] def peq (n : Nat) (t u : Array Nat) : Bool := allBelowN n fun i => t[i]! == u[i]!

@[expose] def pisInv (n : Nat) (t r : Array Nat) : Bool :=
  allBelowN n fun i => decide (t[i]! < n) && r[t[i]!]! == i

@[expose] def pinvCand (n : Nat) (t : Array Nat) : Array Nat := Id.run do
  let mut r : Array Nat := Array.replicate n 0
  for i in [0:n] do
    r := r.set! t[i]! i
  return r

@[expose] def pinvs (n : Nat) (S : Array (Array Nat)) : Array (Array Nat) := S.map (pinvCand n)

@[inline, expose] def pletter (S Sinv : Array (Array Nat)) (l : Int) : Array Nat :=
  if 0 < l then S[l.toNat - 1]! else Sinv[(-l).toNat - 1]!

@[expose] def pword (n : Nat) (S Sinv : Array (Array Nat)) : List Int → Array Nat
  | [] => pid n
  | l :: w => pcomp n (pletter S Sinv l) (pword n S Sinv w)

@[expose] def pwords (n : Nat) (S Sinv : Array (Array Nat)) (ws : Array (List Int)) :
    Array (Array Nat) := Id.run do
  let mut r : Array (Array Nat) := Array.mkEmpty ws.size
  for w in ws do
    r := r.push (pword n S Sinv w)
  return r

@[expose] def commGens (n : Nat) (g : Array (Array Nat)) (specs : Array (Nat × Nat × Nat)) :
    Array (Array Nat) := Id.run do
  let mut r : Array (Array Nat) := Array.mkEmpty specs.size
  for (a, b, k) in specs do
    let ga := g[a - 1]!
    let gb := g[b - 1]!
    let x := pcomp n gb (pcomp n ga (pcomp n (pinvCand n gb) (pinvCand n ga)))
    r := r.push (if k == 0 then x else pcomp n g[k - 1]! (pcomp n x (pinvCand n g[k - 1]!)))
  return r

@[expose] def conjAll (n : Nat) (c ci : Array Nat) (g : Array (Array Nat)) :
    Array (Array Nat) := Id.run do
  let mut r : Array (Array Nat) := Array.mkEmpty g.size
  for x in g do
    r := r.push (pcomp n c (pcomp n x ci))
  return r

@[expose] def plettersOK (j : Nat) (w : List Int) : Bool :=
  w.all fun l => l != 0 && decide (l.natAbs ≤ j)

@[expose] def extendStrong (n : Nat) (orig : Array (Array Nat)) (W : Array (List Int)) :
    Array (Array Nat) := Id.run do
  let mut S : Array (Array Nat) := orig
  let mut Si : Array (Array Nat) := orig.map (pinvCand n)
  for j in [orig.size:W.size] do
    let s := pword n S Si W[j]!
    S := S.push s
    Si := Si.push (pinvCand n s)
  return S

@[expose] def pfixes (base : Array Nat) (t : Array Nat) (i : Nat) : Bool :=
  allBelowN i fun k => t[base[k]!]! == base[k]!

@[expose] def levIdx (S : Array (Array Nat)) (base : Array Nat) (i : Nat) : List Nat :=
  (List.range S.size).filter fun j => pfixes base S[j]! i

@[expose] def levSteps (S Sinv : Array (Array Nat)) (base : Array Nat) (i : Nat) :
    Array (Array Nat) :=
  ((levIdx S base i).map fun j => S[j]!).toArray ++
    ((levIdx S base i).map fun j => Sinv[j]!).toArray

@[expose] def levInvSteps (S Sinv : Array (Array Nat)) (base : Array Nat) (i : Nat) :
    Array (Array Nat) :=
  ((levIdx S base i).map fun j => Sinv[j]!).toArray ++
    ((levIdx S base i).map fun j => S[j]!).toArray

structure CLevel where
  pts : Array Nat
  pos : Array Nat
  par : Array Nat
  lab : Array Nat
deriving Inhabited

@[expose] def cbfs (n root : Nat) (steps : Array (Array Nat)) : CLevel := Id.run do
  let mut pos : Array Nat := (Array.replicate n n).set! root 0
  let mut pts : Array Nat := #[root]
  let mut par : Array Nat := #[0]
  let mut lab : Array Nat := #[0]
  for h in [0:n] do
    if h < pts.size then
      let x := pts[h]!
      for j in [0:steps.size] do
        let y := (steps[j]!)[x]!
        if pos[y]! == n then
          pos := pos.set! y pts.size
          pts := pts.push y
          par := par.push h
          lab := lab.push j
    else
      break
  return ⟨pts, pos, par, lab⟩

@[inline, expose] def plexLt (a b c d : Nat) : Bool := a < c || (a == c && b < d)

@[expose] def clevelOK (n root : Nat) (steps : Array (Array Nat)) (L : CLevel) : Bool :=
  let m := L.pts.size
  let r := steps.size
  decide (0 < m) && decide (m ≤ n) && L.pts[0]! == root &&
    allBelowN m (fun k => decide (L.pts[k]! < n) && L.pos[L.pts[k]!]! == k) &&
    allBelowN n (fun z => !(decide (L.pos[z]! < m)) || L.pts[L.pos[z]!]! == z) &&
    allBelowN m (fun k => k == 0 || (decide (L.par[k]! < k) && decide (L.lab[k]! < r) &&
      (steps[L.lab[k]!]!)[L.pts[L.par[k]!]!]! == L.pts[k]!)) &&
    allBelowN m (fun k => k == 0 || !(decide (k + 1 < m)) ||
      plexLt L.par[k]! L.lab[k]! L.par[k + 1]! L.lab[k + 1]!) &&
    allBelowN m (fun h => allBelowN r fun j =>
      let k := L.pos[(steps[j]!)[L.pts[h]!]!]!
      decide (k < m) && (k == 0 || !(plexLt h j L.par[k]! L.lab[k]!)))

@[expose] def trApp (steps : Array (Array Nat)) (L : CLevel) : Nat → Nat → Nat → Nat
  | 0, _, p => p
  | fuel + 1, k, p =>
    if k == 0 then p else (steps[L.lab[k]!]!)[trApp steps L fuel L.par[k]! p]!

@[expose] def trInvApp (invSteps : Array (Array Nat)) (L : CLevel) : Nat → Nat → Nat → Nat
  | 0, _, p => p
  | fuel + 1, k, p =>
    if k == 0 then p else trInvApp invSteps L fuel L.par[k]! ((invSteps[L.lab[k]!]!)[p]!)

@[expose] def cLevels (n : Nat) (base : Array Nat) (stepsAll : Array (Array (Array Nat))) :
    Array CLevel :=
  Array.ofFn (n := base.size) fun i => cbfs n base[i.val]! stepsAll[i.val]!


@[expose] def allSteps (S Sinv : Array (Array Nat)) (base : Array Nat) :
    Array (Array (Array Nat)) :=
  Array.ofFn (n := base.size) fun i => levSteps S Sinv base i.val

@[expose] def allInvSteps (S Sinv : Array (Array Nat)) (base : Array Nat) :
    Array (Array (Array Nat)) :=
  Array.ofFn (n := base.size) fun i => levInvSteps S Sinv base i.val

@[expose] def psift (levels : Array CLevel) (invs : Array (Array (Array Nat)))
    (pts bidx : Array Nat) (full : Bool) (l : Nat) (img : Array Nat) : Bool :=
  if _h : l < levels.size then
    let L := levels[l]
    let k := L.pos[img[bidx[l]!]!]!
    decide (k < L.pts.size) &&
      psift levels invs pts bidx full (l + 1)
        (img.map fun y => trInvApp invs[l]! L L.pts.size k y)
  else !full || allBelowN pts.size fun t => img[t]! == pts[t]!
termination_by levels.size - l

@[expose] def schreierImgs (steps invs : Array (Array Nat)) (L : CLevel) (pts : Array Nat)
    (h j k : Nat) : Array Nat :=
  pts.map fun p => trInvApp invs L L.pts.size k ((steps[j]!)[trApp steps L L.pts.size h p]!)

@[expose] def cschreierOK (levels : Array CLevel) (stepsAll invAll : Array (Array (Array Nat)))
    (pts bidx : Array Nat) (full : Bool) (i : Nat) (chunks : Nat) : Bool :=
  let L := levels[i]!
  let steps := stepsAll[i]!
  let invs := invAll[i]!
  parBelow L.pts.size chunks fun h => allBelowN steps.size fun j =>
    let k := L.pos[(steps[j]!)[L.pts[h]!]!]!
    decide (k < L.pts.size) &&
      psift levels invAll pts bidx full (i + 1) (schreierImgs steps invs L pts h j k)

@[expose] def chainOK (n m : Nat) (S : Array (Array Nat)) (base : Array Nat)
    (W : Array (List Int)) (pts bidx : Array Nat) (full : Bool) (chunks : Nat) : Bool :=
  let Sinv := pinvs n S
  let stepsAll := allSteps S Sinv base
  let invAll := allInvSteps S Sinv base
  let levels := cLevels n base stepsAll
  decide (m ≤ S.size) && W.size == S.size &&
    allBelowN S.size (fun j => pisInv n S[j]! Sinv[j]!) &&
    allBelowN S.size (fun j => decide (j < m) ||
      (plettersOK j W[j]! && peq n S[j]! (pword n S Sinv W[j]!))) &&
    allBelowN base.size (fun i => decide (base[i]! < n)) &&
    bidx.size == base.size &&
    allBelowN base.size (fun i => decide (bidx[i]! < pts.size) && pts[bidx[i]!]! == base[i]!) &&
    allBelowN pts.size (fun t => decide (pts[t]! < n)) &&
    (!full || allBelowN S.size fun j => !(pfixes base S[j]! base.size) || peq n S[j]! (pid n)) &&
    allBelowN base.size (fun i => clevelOK n base[i]! stepsAll[i]! levels[i]!) &&
    allBelowN base.size (fun i => cschreierOK levels stepsAll invAll pts bidx full i chunks)

@[expose] def pointChainOK (n m : Nat) (S : Array (Array Nat)) (base : Array Nat)
    (W : Array (List Int)) (chunks : Nat) : Bool :=
  chainOK n m S base W base (Array.ofFn (n := base.size) fun i => i.val) false chunks

@[expose] def fullChainOK (n m : Nat) (S : Array (Array Nat)) (base : Array Nat)
    (W : Array (List Int)) (chunks : Nat) : Bool :=
  chainOK n m S base W (pid n) base true chunks

@[expose] def cOrbitSizes (n : Nat) (S : Array (Array Nat)) (base : Array Nat) : List Nat :=
  (cLevels n base (allSteps S (pinvs n S) base)).toList.map fun L => L.pts.size

@[expose] def memPoint (levels : Array CLevel) (invAll : Array (Array (Array Nat)))
    (base : Array Nat) (g : Array Nat) : Bool :=
  psift levels invAll base (Array.ofFn (n := base.size) fun i => i.val) false 0
    (base.map fun b => g[b]!)

@[expose] def memFull (n : Nat) (levels : Array CLevel) (invAll : Array (Array (Array Nat)))
    (base : Array Nat) (g : Array Nat) : Bool :=
  psift levels invAll (pid n) base true 0 (Array.ofFn (n := n) fun i => g[i.val]!)

@[expose] def tr2App (levels : Array CLevel) (stepsAll : Array (Array (Array Nat)))
    (i₁ i₂ k₁ k₂ p : Nat) : Nat :=
  trApp stepsAll[i₁]! levels[i₁]! levels[i₁]!.pts.size k₁
    (trApp stepsAll[i₂]! levels[i₂]! levels[i₂]!.pts.size k₂ p)

@[expose] def commCount (levels : Array CLevel) (stepsAll : Array (Array (Array Nat)))
    (i₁ i₂ : Nat) (z tpts : Array Nat) : Nat :=
  ((List.range levels[i₁]!.pts.size).map fun k₁ =>
    ((List.range levels[i₂]!.pts.size).filter fun k₂ =>
      tpts.all fun p => tr2App levels stepsAll i₁ i₂ k₁ k₂ z[p]! ==
        z[tr2App levels stepsAll i₁ i₂ k₁ k₂ p]!).length).sum

end CFSG.ONSchreier.Native
