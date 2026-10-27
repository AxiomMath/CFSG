module

public import Certificates.Data.CFSGNative.MonsterB.Co2Data

public section

namespace CFSG.Monster.B.Co2.Native

@[inline, expose] def allLt (n : Nat) (p : Nat → Bool) : Bool := Nat.all n fun i _ => p i

@[expose] def parLt (n chunks : Nat) (p : Nat → Bool) : Bool :=
  let sz := n / chunks + 1
  ((List.range chunks).map fun c => Task.spawn fun _ =>
    allLt sz fun k => !(decide (c * sz + k < n)) || p (c * sz + k)).all Task.get

@[expose] def compA (n : Nat) (t u : Array Nat) : Array Nat :=
  Array.ofFn (n := n) fun i => t[u[i.val]!]!

@[expose] def idA (n : Nat) : Array Nat := Array.ofFn (n := n) fun i => i.val

@[expose] def eqA (n : Nat) (t u : Array Nat) : Bool := allLt n fun i => t[i]! == u[i]!

@[expose] def isInvA (n : Nat) (t r : Array Nat) : Bool :=
  allLt n fun i => decide (t[i]! < n) && r[t[i]!]! == i

@[expose] def invCand (n : Nat) (t : Array Nat) : Array Nat := Id.run do
  let mut r : Array Nat := Array.replicate n 0
  for i in [0:n] do
    r := r.set! t[i]! i
  return r

@[inline, expose] def letterA (S Sinv : Array (Array Nat)) (l : Int) : Array Nat :=
  if 0 < l then S[l.toNat - 1]! else Sinv[(-l).toNat - 1]!

@[expose] def wordA (n : Nat) (S Sinv : Array (Array Nat)) : List Int → Array Nat
  | [] => idA n
  | l :: w => compA n (letterA S Sinv l) (wordA n S Sinv w)

@[expose] def lettersOK (j : Nat) (w : List Int) : Bool :=
  w.all fun l => l != 0 && decide (l.natAbs ≤ j)

@[expose] def fixesFirst (base : Array Nat) (t : Array Nat) (i : Nat) : Bool :=
  allLt i fun k => t[base[k]!]! == base[k]!

@[expose] def levelIdx (S : Array (Array Nat)) (base : Array Nat) (i : Nat) : List Nat :=
  (List.range S.size).filter fun j => fixesFirst base S[j]! i

@[expose] def levelSteps (S Sinv : Array (Array Nat)) (base : Array Nat) (i : Nat) :
    Array (Array Nat) :=
  ((levelIdx S base i).map fun j => S[j]!).toArray ++
    ((levelIdx S base i).map fun j => Sinv[j]!).toArray

structure Level where
  pts : Array Nat
  pos : Array Nat
  par : Array Nat
  lab : Array Nat
  tr : Array (Array Nat)
  trInv : Array (Array Nat)
deriving Inhabited

@[expose] def bfs (n root : Nat) (steps : Array (Array Nat)) : Level := Id.run do
  let mut pos : Array Nat := (Array.replicate n n).set! root 0
  let mut pts : Array Nat := #[root]
  let mut par : Array Nat := #[0]
  let mut lab : Array Nat := #[0]
  let mut tr : Array (Array Nat) := #[idA n]
  for h in [0:n] do
    if h < pts.size then
      let x := pts[h]!
      for j in [0:steps.size] do
        let s := steps[j]!
        let y := s[x]!
        if pos[y]! == n then
          pos := pos.set! y pts.size
          pts := pts.push y
          par := par.push h
          lab := lab.push j
          tr := tr.push (compA n s tr[h]!)
    else
      break
  return ⟨pts, pos, par, lab, tr, tr.map (invCand n)⟩

@[inline, expose] def lexLt (a b c d : Nat) : Bool := a < c || (a == c && b < d)

@[expose] def levelOK (n root : Nat) (steps : Array (Array Nat)) (L : Level) : Bool :=
  let m := L.pts.size
  let r := steps.size
  decide (0 < m) && decide (m ≤ n) && L.pts[0]! == root &&
    allLt m (fun k => decide (L.pts[k]! < n) && L.pos[L.pts[k]!]! == k) &&
    allLt n (fun z => !(decide (L.pos[z]! < m)) || L.pts[L.pos[z]!]! == z) &&
    allLt m (fun k => k == 0 || (decide (L.par[k]! < k) && decide (L.lab[k]! < r) &&
      (steps[L.lab[k]!]!)[L.pts[L.par[k]!]!]! == L.pts[k]!)) &&
    allLt m (fun k => k == 0 || !(decide (k + 1 < m)) ||
      lexLt L.par[k]! L.lab[k]! L.par[k + 1]! L.lab[k + 1]!) &&
    allLt m (fun h => allLt r fun j =>
      let k := L.pos[(steps[j]!)[L.pts[h]!]!]!
      decide (k < m) && (k == 0 || !(lexLt h j L.par[k]! L.lab[k]!))) &&
    eqA n L.tr[0]! (idA n) &&
    allLt m (fun k => k == 0 || eqA n L.tr[k]! (compA n steps[L.lab[k]!]! L.tr[L.par[k]!]!)) &&
    allLt m (fun k => isInvA n L.tr[k]! L.trInv[k]!)

@[expose] def siftA (n : Nat) (levels : Array Level) (base : Array Nat) (l : Nat)
    (g : Array Nat) : Bool :=
  if _h : l < levels.size then
    let L := levels[l]
    let k := L.pos[g[base[l]!]!]!
    decide (k < L.pts.size) && siftA n levels base (l + 1) (compA n L.trInv[k]! g)
  else eqA n g (idA n)
termination_by levels.size - l

@[expose] def schreierOK (n : Nat) (levels : Array Level) (base : Array Nat) (i : Nat)
    (steps : Array (Array Nat)) (L : Level) (chunks : Nat) : Bool :=
  parLt L.pts.size chunks fun h => allLt steps.size fun j =>
    let s := steps[j]!
    let k := L.pos[s[L.pts[h]!]!]!
    decide (k < L.pts.size) && siftA n levels base (i + 1) (compA n L.trInv[k]! (compA n s L.tr[h]!))

@[expose] def deg (_ : Unit := ()) : Nat := 2300

@[expose] def strongInv (_ : Unit := ()) : Array (Array Nat) := chainStrong.map (invCand deg)

@[expose] def chainSteps (i : Nat) : Array (Array Nat) :=
  levelSteps chainStrong strongInv chainBase i

@[expose] def chainLevels (_ : Unit := ()) : Array Level :=
  Array.ofFn (n := 10) fun i => bfs deg chainBase[i.val]! (chainSteps i.val)

@[expose] def orbitLengths : Array Nat := #[2300, 891, 336, 160, 6, 4, 2, 2, 2, 2]

@[expose] def chainCheck (chunks : Nat) : Bool :=
  let n := deg
  let S := chainStrong
  let Sinv := strongInv
  let levels := chainLevels
  pairPerms.size == 2 && S.size == chainStrongCount && chainWords.size == chainStrongCount &&
    chainBase.size == 10 && levels.size == 10 &&
    allLt 2 (fun j => isInvA n pairPerms[j]! (invCand n pairPerms[j]!)) &&
    allLt S.size (fun j => isInvA n S[j]! Sinv[j]!) &&
    eqA n S[0]! pairPerms[0]! && eqA n S[1]! pairPerms[1]! &&
    allLt S.size (fun j => decide (j < 2) ||
      (lettersOK j chainWords[j]! && eqA n S[j]! (wordA n S Sinv chainWords[j]!))) &&
    allLt S.size (fun j => !(fixesFirst chainBase S[j]! 10) || eqA n S[j]! (idA n)) &&
    allLt 10 (fun i => decide (chainBase[i]! < n)) &&
    allLt 10 (fun i => levelOK n chainBase[i]! (chainSteps i) levels[i]! &&
      levels[i]!.pts.size == orbitLengths[i]!) &&
    allLt 10 (fun i => schreierOK n levels chainBase i (chainSteps i) levels[i]! chunks)

@[expose] def orbitRecord (n root : Nat) (gens : Array (Array Nat)) :
    Array Nat × Array Nat × Array Nat := Id.run do
  let mut dep : Array Nat := (Array.replicate n 0).set! root 1
  let mut par : Array Nat := Array.replicate n 0
  let mut lab : Array Nat := Array.replicate n 0
  let mut q : Array Nat := #[root]
  for h in [0:n] do
    if h < q.size then
      let x := q[h]!
      for j in [0:gens.size] do
        let y := (gens[j]!)[x]!
        if dep[y]! == 0 then
          dep := dep.set! y (dep[x]! + 1)
          par := par.set! y x
          lab := lab.set! y j
          q := q.push y
    else
      break
  return (dep, par, lab)

@[expose] def orbitLabel (n : Nat) (orbs : Array (Array Nat)) : Array Nat × Array Nat := Id.run do
  let mut lab : Array Nat := Array.replicate n 3
  let mut ps : Array Nat := Array.replicate n 0
  for t in [0:orbs.size] do
    for k in [0:orbs[t]!.size] do
      lab := lab.set! (orbs[t]!)[k]! t
      ps := ps.set! (orbs[t]!)[k]! k
  return (lab, ps)

@[expose] def orbitsOK (n : Nat) (gens : Array (Array Nat)) (orbs : Array (Array Nat))
    (sizes lb ps : Array Nat) (recs : Array (Array Nat × Array Nat × Array Nat)) : Bool :=
  orbs.size == 3 && sizes.size == 3 && recs.size == 3 &&
    allLt 3 (fun t => orbs[t]!.size == sizes[t]! && decide (0 < sizes[t]!) &&
      allLt sizes[t]! (fun k => decide ((orbs[t]!)[k]! < n) && lb[(orbs[t]!)[k]!]! == t) &&
      allLt (sizes[t]! - 1) (fun k => decide ((orbs[t]!)[k]! < (orbs[t]!)[k + 1]!))) &&
    allLt n (fun z => decide (lb[z]! < 3) && decide (ps[z]! < sizes[lb[z]!]!) &&
      (orbs[lb[z]!]!)[ps[z]!]! == z) &&
    allLt 3 (fun t => allLt sizes[t]! fun k => allLt gens.size fun j =>
      decide ((gens[j]!)[(orbs[t]!)[k]!]! < n) && lb[(gens[j]!)[(orbs[t]!)[k]!]!]! == t) &&
    allLt 3 (fun t => allLt sizes[t]! fun k =>
      decide (0 < recs[t]!.1[(orbs[t]!)[k]!]!) &&
        (if recs[t]!.1[(orbs[t]!)[k]!]! == 1 then (orbs[t]!)[k]! == (orbs[t]!)[0]! else
          decide (recs[t]!.2.1[(orbs[t]!)[k]!]! < n) &&
          lb[recs[t]!.2.1[(orbs[t]!)[k]!]!]! == t &&
          recs[t]!.1[recs[t]!.2.1[(orbs[t]!)[k]!]!]! + 1 == recs[t]!.1[(orbs[t]!)[k]!]! &&
          decide (recs[t]!.2.2[(orbs[t]!)[k]!]! < gens.size) &&
          (gens[recs[t]!.2.2[(orbs[t]!)[k]!]!]!)[recs[t]!.2.1[(orbs[t]!)[k]!]!]! ==
            (orbs[t]!)[k]!))

@[expose] def stabGens (_ : Unit := ()) : Array (Array Nat) := chainStabIdx.map fun j => chainStrong[j]!

@[expose] def stabCheck (_ : Unit := ()) : Bool :=
  let n := deg
  let lbps := orbitLabel n chainOrbits
  let recs := chainOrbits.map fun o => orbitRecord n o[0]! stabGens
  chainBase[0]! == 0 && (chainOrbits[0]!)[0]! == 0 &&
    allLt chainStabIdx.size (fun k => decide (chainStabIdx[k]! < chainStrong.size)) &&
    allLt (chainStabIdx.size - 1) (fun k => decide (chainStabIdx[k]! < chainStabIdx[k + 1]!)) &&
    allLt chainStrong.size (fun j => ((chainStrong[j]!)[0]! == 0) == chainStabIdx.contains j) &&
    orbitsOK n stabGens chainOrbits chainOrbitSizes lbps.1 lbps.2 recs

@[expose] def recordWordOK (r : GenRecord) : Bool :=
  match r.kind with
  | .pairStabilizer => r.word.all fun l => l == 1 || l == 2 || l == -1 || l == -2
  | _ => r.word.all fun l => decide (0 ≤ l) && decide (l ≤ 14)

@[expose] def dataCheck (_ : Unit := ()) : Bool :=
  genRecords.size == 24 && quotientBasis.size == 22 && pairWords.size == 2 &&
    allLt 24 (fun i => genRecords[i]!.matrix.size == 24 &&
      genRecords[i]!.quotientMatrix.size == 22 && recordWordOK genRecords[i]!) &&
    allLt 24 (fun i => isInvA deg permutations[i]! (invCand deg permutations[i]!)) &&
    allLt 2 (fun i => isInvA deg pairPerms[i]! (invCand deg pairPerms[i]!)) &&
    allLt 2 (fun i => pairWords[i]!.all fun l => l != 0 && decide (l.natAbs ≤ 24))

@[expose] def co2ChainCertOK (_ : Unit := ()) : Bool := chainCheck 8 && stabCheck

end CFSG.Monster.B.Co2.Native
