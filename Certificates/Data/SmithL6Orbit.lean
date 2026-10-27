module

public import Certificates.Data.SmithL6Check

public section

namespace CFSG.SmithL6

open CFSG.SmithE (applyCols)

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

@[expose] def ugens : Array Nat := #[189, 193, 201, 158, 162, 170, 127, 131, 139]

@[expose] def uco : Array Nat := #[9, 18, 27, 36, 45, 54, 63, 65, 130, 195, 260, 325, 390, 455, 72,
  144, 216, 288, 360, 432, 504, 73, 146, 219, 292, 365, 438, 511, 64, 128, 192, 256, 320, 384, 448,
  8, 16, 24, 32, 40, 48, 56, 1, 2, 3, 4, 5, 6, 7]

@[expose] def uaWord (a x : Nat) : Nat :=
  (List.range 9).foldr (fun j y => if a.testBit j then tvTab[ugens[j]!]![y]! else y) x

@[expose] def chkUa : Bool :=
  let P0 := planePtsArr[0]!
  ugens.size == 9 && uco.size == 49 && ugens.all (fun g => decide (g < 1953) && inPlane 0 g) &&
  (List.range 49).all (fun k => decide (0 < uco[k]!) && decide (uco[k]! < 512) &&
    (List.range k).all fun l => uco[l]! != uco[k]!) &&
  P0.all (fun p => P0.all fun q => tvTab[p]![q]! == q) &&
  (List.range 49).all (fun k => (List.range 1953).all fun x =>
    uaWord uco[k]! x == tvTab[P0[k]!]![x]!) &&
  (List.range 512).all (fun a => a == 0 || (List.range 1953).any fun x => uaWord a x != x) &&
  (List.range 1953).all (fun q => !(P0.all fun p => tvTab[p]![q]! == q) || inPlane 0 q) &&
  (List.range 1395).all fun j => j == 0 || P0.any fun p => planeImg p j != j

@[expose] def elemGens : Array Nat :=
  ((List.range 6).flatMap fun i => (List.range 6).filterMap fun j =>
    if i == j then none else some tvIdxTab[64 * 2 ^ i + 2 ^ j]!).toArray

@[expose] def stabGens : Array Nat := ((List.range 1953).filter fun p => planeImg p 0 == 0).toArray

@[expose] def chkTrans : Bool :=
  elemGens.all (· < 1953) &&
  treeOK 1395 elemGens.size (fun j => j == 0)
    (fun g j' j => planeImg elemGens[g]! j' == j)
    (treeBFS 1395 (Array.range elemGens.size) (fun g j => planeImg elemGens[g]! j) [0])

@[expose] def dRoot (c : Nat) : Nat := ((List.range 1395).find? fun j => meetCard 0 j == c).getD 0

@[expose] def chkPlaneOrbits : Bool :=
  treeOK 1395 stabGens.size (fun j => j == dRoot (meetCard 0 j))
    (fun g j' j => meetCard 0 j' == meetCard 0 j && planeImg stabGens[g]! j' == j)
    (treeBFS 1395 (Array.range stabGens.size) (fun g j => planeImg stabGens[g]! j)
      [dRoot 49, dRoot 9, dRoot 1, dRoot 0])

@[expose] def uSums : Array Bool :=
  Array.ofFn (n := 512) fun v => (List.range 49).any fun k => (List.range 49).any fun l =>
    k != l && uco[k]! ^^^ uco[l]! == v.val

@[expose] def uCls (S2 : Array Bool) (v : Nat) : Nat :=
  if v == 0 then 0 else if uco.contains v then 1 else if S2[v]! then 2 else 3

@[expose] def uRoot (S2 : Array Bool) (c : Nat) : Nat :=
  ((List.range 512).find? fun v => uCls S2 v == c).getD 0

@[expose] def pos0 (q : Nat) : Nat := planePtsArr[0]!.findIdx (· == q)

@[expose] def ucols (p : Nat) : Array Nat :=
  Array.ofFn (n := 9) fun j => uco[pos0 tvTab[p]![ugens[j.val]!]!]!

@[expose] def ucolsArr : Array (Array Nat) := stabGens.map ucols

@[expose] def chkUOrbits : Bool :=
  let S2 := uSums
  let ucs := ucolsArr
  uCls S2 0 == 0 &&
  (List.range 512).countP (fun v => uCls S2 v == 1) == 49 &&
  (List.range 512).countP (fun v => uCls S2 v == 2) == 294 &&
  (List.range 512).countP (fun v => uCls S2 v == 3) == 168 &&
  treeOK 512 stabGens.size (fun v => v == uRoot S2 (uCls S2 v))
    (fun g u v => uCls S2 u == uCls S2 v && applyCols ucs[g]! u == v)
    (treeBFS 512 (Array.range stabGens.size) (fun g v => applyCols ucs[g]! v)
      [uRoot S2 1, uRoot S2 2, uRoot S2 3])

end CFSG.SmithL6
