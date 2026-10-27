module

public import Certificates.Data.SuzLevelTwoCoverInputs
public import CFSG.Sporadic.SuzRecog.LevelTwoCheck

public section

namespace CFSG.Sporadic.SuzRecog.LevelTwoCover

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Sporadic.SuzRecog.LevelTwoData
  CFSG.Sporadic.SuzRecog.LevelTwoCoverData CFSG.Sporadic.SuzRecog.ElimCert
  CFSG.Sporadic.SuzRecog.LevelTwo

@[expose] def coverList (nb : Array (Array Nat)) (vo : Array Nat) (u : Nat) : Array Nat :=
  if u % 2997 < 2835 then
    Array.ofFn (n := 36) fun k =>
      (nb[u % 2997]!)[k.val]! + 2997 * ((u / 2997 + vo[36 * (u % 2997) + k.val]!) % 3)
  else #[]

@[expose] def coverLists (nb : Array (Array Nat)) (vo : Array Nat) : Array (Array Nat) :=
  Array.ofFn (n := 8991) fun u => coverList nb vo u.val

@[expose] def nbrC : Array (Array Nat) := coverLists nbr volt

@[expose] def liftOf (vt sh : Array Nat) : Array Nat :=
  Array.ofFn (n := 8991) fun u =>
    vt[u.val % 2997]! + 2997 * ((u.val / 2997 + sh[u.val % 2997]!) % 3)

@[expose] def liftArr (s : Nat) : Array Nat := liftOf (vtab s) (shift s)

@[expose] def deckArr : Array Nat := Array.ofFn (n := 8991) fun u => (u.val + 2997) % 8991

@[expose] def presAdj (nb : Array (Array Nat)) (L : Array Nat) : Bool :=
  allLt 8991 fun u => allLt (nb[u]!).size fun k => adjB nb L[u]! L[(nb[u]!)[k]!]!

@[expose] def triC (nb : Array (Array Nat)) (x y z : Nat) : Bool :=
  adjB nb x y && adjB nb y z && adjB nb x z &&
    ((if 2835 ≤ x % 2997 then 1 else 0) + (if 2835 ≤ y % 2997 then 1 else 0) +
      (if 2835 ≤ z % 2997 then 1 else 0) == 1)

@[expose] def symNbrOf (nb : Array (Array Nat)) : Array (Array Nat) := Id.run do
  let mut out : Array (Array Nat) := Array.replicate 8991 #[]
  for x in [0:8991] do
    for y in nb[x]! do
      out := out.modify x (·.push y)
      out := out.modify y (·.push x)
  return out

@[expose] def bfsOf (sym : Array (Array Nat)) : Array Nat × Array Nat := Id.run do
  let mut par : Array Nat := Array.replicate 8991 0
  let mut dep : Array Nat := Array.replicate 8991 8991
  let mut queue : Array Nat := #[0]
  dep := dep.set! 0 0
  for h in [0:8991] do
    if h < queue.size then
      let x := queue[h]!
      for y in sym[x]! do
        if dep[y]! == 8991 then
          dep := dep.set! y (dep[x]! + 1)
          par := par.set! y x
          queue := queue.push y
  return (par, dep)

@[expose] def bfsC : Array Nat × Array Nat := bfsOf (symNbrOf nbrC)

@[expose] def treeParC : Array Nat := bfsC.1

@[expose] def treeDepC : Array Nat := bfsC.2

@[expose] def posOf (nb : Array (Array Nat)) (x y : Nat) : Nat :=
  ((nb[x]!).findIdx? (· == y)).getD 36

@[expose] def eidOf (nb : Array (Array Nat)) (x y : Nat) : Nat :=
  if x % 2997 < 2835 && (2835 ≤ y % 2997 || x % 2997 < y % 2997) then x * 36 + posOf nb x y
  else y * 36 + posOf nb y x

@[expose] def cellsOf (nb : Array (Array Nat)) (cs : Array (Nat × Nat × Nat)) (vo : Array Nat) :
    Array (Nat × Nat × Nat) × Array (Nat × Nat × Nat) := Id.run do
  let mut out : Array (Nat × Nat × Nat) := #[]
  let mut ids : Array (Nat × Nat × Nat) := #[]
  for c in cs do
    let (x, y, z) := c
    let kxy := ((nb[x]!).findIdx? (· == y)).getD 36
    let kxz := ((nb[x]!).findIdx? (· == z)).getD 36
    let kyz := ((nb[y]!).findIdx? (· == z)).getD 36
    let vxy := vo[36 * x + kxy]! % 3
    let vxz := vo[36 * x + kxz]! % 3
    let vyz := vo[36 * y + kyz]! % 3
    if (vxy + vyz + 3 - vxz) % 3 == 0 then
      for i in [0:3] do
        let x' := x + 2997 * i
        let y' := y + 2997 * ((i + vxy) % 3)
        let z' := z + 2997 * ((i + vxz) % 3)
        out := out.push (x', y', z')
        ids := ids.push (x' * 36 + kxy, x' * 36 + kxz, y' * 36 + kyz)
  return (out, ids)

@[expose] def cellsC : Array (Nat × Nat × Nat) × Array (Nat × Nat × Nat) :=
  cellsOf nbr cells.1 volt

@[expose] def treeEidsOf (nb : Array (Array Nat)) (par : Array Nat) : Array Nat :=
  Array.ofFn (n := 8991) fun z => eidOf nb par[z.val]! z.val

@[expose] def elimCoreC (cs ids : Array (Nat × Nat × Nat)) (par tids : Array Nat) :
    Array (Array Nat) × Array Nat := Id.run do
  let ne := 8991 * 36
  let mut steps : Array (Array Nat) := #[]
  let mut stepOf : Array Nat := Array.replicate ne 0
  let mut done : Array Bool := Array.replicate ne false
  for z in [1:8991] do
    let e := tids[z]!
    stepOf := stepOf.set! e steps.size
    done := done.set! e true
    steps := steps.push #[par[z]!, z]
  let mut ecells : Array (Array Nat) := Array.replicate ne #[]
  for c in [0:cs.size] do
    let (e₁, e₂, e₃) := ids[c]!
    ecells := ecells.modify e₁ (·.push c)
    ecells := ecells.modify e₂ (·.push c)
    ecells := ecells.modify e₃ (·.push c)
  let mut queue : Array Nat := #[]
  for c in [0:cs.size] do
    let (e₁, e₂, e₃) := ids[c]!
    if (if done[e₁]! then 0 else 1) + (if done[e₂]! then 0 else 1) +
        (if done[e₃]! then 0 else 1) == 1 then
      queue := queue.push c
  for h in [0:4 * cs.size] do
    if h < queue.size then
      let c := queue[h]!
      let (e₁, e₂, e₃) := ids[c]!
      if (if done[e₁]! then 0 else 1) + (if done[e₂]! then 0 else 1) +
          (if done[e₃]! then 0 else 1) == 1 then
        let (a, b, v) := cs[c]!
        let (x, z, y, e, f₁, f₂) := if !done[e₁]! then (a, b, v, e₁, e₂, e₃)
          else if !done[e₂]! then (a, v, b, e₂, e₁, e₃) else (b, v, a, e₃, e₁, e₂)
        stepOf := stepOf.set! e steps.size
        done := done.set! e true
        steps := steps.push #[x, z, y, stepOf[f₁]!, stepOf[f₂]!]
        for c' in ecells[e]! do
          let (d₁, d₂, d₃) := ids[c']!
          if (if done[d₁]! then 0 else 1) + (if done[d₂]! then 0 else 1) +
              (if done[d₃]! then 0 else 1) == 1 then
            queue := queue.push c'
  return (steps, stepOf)

@[expose] def elimRunC : Array (Array Nat) × Array Nat :=
  elimCoreC cellsC.1 cellsC.2 treeParC (treeEidsOf nbrC treeParC)

@[expose] def elimStepsC : Array (Array Nat) := elimRunC.1

@[expose] def emapOf (nb : Array (Array Nat)) (st : Array Nat) : Array (Array Nat) :=
  Array.ofFn (n := 8991) fun x => nb[x.val]!.map fun y => st[eidOf nb x.val y]!

@[expose] def elimEmapC : Array (Array Nat) := emapOf nbrC elimRunC.2

@[expose] def liftAt0 (y : Nat) : Nat := (nbrC[0]!)[posIn 0 y]!

@[expose] def p1c : Nat := liftAt0 p1

@[expose] def qc : Nat := liftAt0 2835

@[expose] def cellc (k : Nat) : Nat := liftAt0 cellReps[k]!

@[expose] def cellVert' (k : Nat) : Nat := actV (cellC' k).1 (cellC' k).2 2835

@[expose] def cellc' (k : Nat) : Nat := liftAt0 (cellVert' k)

@[expose] def listedAt0 (y : Nat) : Bool := posIn 0 y < 36 && (nbr[0]!)[posIn 0 y]! == y

@[expose] def baseOf (nb : Array (Array Nat)) (vo : Array Nat) : Bool :=
  allLt 2835 fun x => (nb[x]!).size == 36 && allLt 36 fun k =>
    decide ((nb[x]!)[k]! < 2997) && (nb[x]!)[k]! != x &&
      allLt k (fun k' => (nb[x]!)[k']! != (nb[x]!)[k]!) &&
      (decide (2835 ≤ (nb[x]!)[k]!) || (List.range 36).any fun k' =>
        (nb[(nb[x]!)[k]!]!)[k']! == x && (vo[36 * x + k]! + vo[36 * (nb[x]!)[k]! + k']!) % 3 == 0)

@[expose] def coverBaseOK : Bool := baseOf nbr volt

@[expose] def coverLiftOK : Bool :=
  allLt 2 fun s => isInvA 8991 (liftArr s) (invCand 8991 (liftArr s)) && presAdj nbrC (liftArr s)

@[expose] def coverDeckOK : Bool :=
  presAdj nbrC deckArr &&
    eqA 1782 (CFSG.Sporadic.SuzOddCore.powA 1782
      (compA 1782 gens[0]! (compA 1782 gens[0]! gens[1]!)) 8) (idA 1782) &&
    eqA 8991 (CFSG.Sporadic.SuzOddCore.powA 8991
      (compA 8991 (liftArr 0) (compA 8991 (liftArr 0) (liftArr 1))) 8) deckArr

@[expose] def coverElimOK : Bool := ok 8991 nbrC treeParC treeDepC (triC nbrC) elimStepsC elimEmapC

@[expose] def coverLocOK : Bool :=
  listedAt0 p1 && listedAt0 2835 &&
    allLt 4 (fun k => listedAt0 cellReps[k]! && listedAt0 (cellVert' k)) &&
    adjB nbrC p1c (cellc 0) && adjB nbrC p1c (cellc 2) && !adjB nbrC p1c (cellc 1) &&
    !adjB nbrC p1c (cellc 3) && adjB nbrC p1c (cellc' 0) && adjB nbrC p1c (cellc' 2)

end CFSG.Sporadic.SuzRecog.LevelTwoCover
