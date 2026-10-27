module

public import CFSG.Sporadic.Schreier.RuCheckInvInputs
public import CFSG.Quasithin.H13.L32ARuU1Inputs
public meta import CFSG.Sporadic.Schreier.RuCheckInvInputs
public meta import CFSG.Quasithin.H13.L32ARuU1Inputs

public section

namespace CFSG.Quasithin.H13.Ch4.G2Ru

open CFSG.Sporadic.RuSchreier CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
  CFSG.Quasithin.H13.KGRu

@[expose] def g2SW (w : List ℤ) : Array ℕ := wordA 4060 ruSGensA (ruSGensA.map ruInv) w

@[expose] def g2WWords : List (List ℤ) :=
  [[3, 4, 3, 4, 3, 4, 3, 4], [-4, 2, 4], [-4, 3, 4], [3, 1, 4, 1, 4], [3, -4, 3, 4, 3],
    [2, -4, 3, 4, 2]]

@[expose] def g2WGenA : Array (Array ℕ) := (g2WWords.map g2SW).toArray

@[expose] def g2WProd (e : ℕ) : Array ℕ :=
  compA 4060 (powA 4060 g2WGenA[0]! (e % 2)) (compA 4060 (powA 4060 g2WGenA[1]! (e / 2 % 2))
    (compA 4060 (powA 4060 g2WGenA[2]! (e / 4 % 2)) (compA 4060 (powA 4060 g2WGenA[3]! (e / 8 % 2))
      (compA 4060 (powA 4060 g2WGenA[4]! (e / 16 % 2)) (powA 4060 g2WGenA[5]! (e / 32 % 2))))))

@[expose] def g2WArr : Array (Array ℕ) := Array.ofFn (n := 64) fun e => g2WProd e.val

@[expose] def g2InW (t : Array ℕ) : Bool := g2WArr.any fun u => eqA 4060 t u

@[expose] def g2NormW (t : Array ℕ) : Bool :=
  let ti := invCand 4060 t
  allLt 6 fun k => g2InW (compA 4060 (compA 4060 t g2WGenA[k]!) ti)

@[expose] def g2ConjWords : List (List ℤ) := [[], [-4], [1], [4]]

@[expose] def g2WrArr : Array (Array (Array ℕ)) :=
  Array.ofFn (n := 4) fun r => g2WArr.map fun u => ruConjA (g2SW (g2ConjWords.getD r.val [])) u

@[expose] def g2Inv : Array (Array ℕ) :=
  ((List.range ruLevS[0]!.pts.size).flatMap fun a =>
    (List.range ruLevS[1]!.pts.size).filterMap fun b =>
      if ruIsInvolA (prod2A 4060 ruLevS a b) then some (prod2A 4060 ruLevS a b) else none).toArray

@[expose] def g2Com (t u : Array ℕ) : Bool :=
  (allLt 16 fun x => t[u[x]!]! == u[t[x]!]!) && eqA 4060 (compA 4060 t u) (compA 4060 u t)

@[expose] def g2ComM : Array (Array Bool) :=
  Array.ofFn (n := g2Inv.size) fun i => Array.ofFn (n := g2Inv.size) fun j =>
    g2Com g2Inv[i.val]! g2Inv[j.val]!

@[expose] def g2Cn (i j : ℕ) : ℕ :=
  (List.range g2Inv.size).countP fun k => (g2ComM[i]!)[k]! && (g2ComM[j]!)[k]!

@[expose] def g2KeepM : Array (Array Bool) :=
  Array.ofFn (n := g2Inv.size) fun i => Array.ofFn (n := g2Inv.size) fun j =>
    (i.val != j.val) && (g2ComM[i.val]!)[j.val]! && decide (63 ≤ g2Cn i.val j.val)

@[expose] def g2DegA : Array ℕ :=
  Array.ofFn (n := g2Inv.size) fun i =>
    (List.range g2Inv.size).countP fun j => (g2KeepM[i.val]!)[j]!

@[expose] def g2InWM : Array (Array Bool) :=
  Array.ofFn (n := 4) fun r => g2Inv.map fun t => g2WrArr[r.val]!.any fun u => eqA 4060 t u

@[expose] def g2Multi (i : ℕ) : Bool := decide (2 ≤ (List.range 4).countP fun r => (g2InWM[r]!)[i]!)

@[expose] def g2E64Local (i : ℕ) : Bool :=
  decide (g2DegA[i]! < 62) || g2Multi i ||
    (List.range 4).any fun r => (g2InWM[r]!)[i]! &&
      allLt g2Inv.size fun j => !(g2KeepM[i]!)[j]! || decide (g2DegA[j]! < 62) || (g2InWM[r]!)[j]!

@[expose] def g2E64Check : Bool :=
  allLt g2Inv.size g2E64Local && decide ((List.range g2Inv.size).countP g2Multi ≤ 62)

@[expose] def g2VWords : List (List ℤ) :=
  [[1, -4, 1, -4, 1, -4, 1, -4], [2, 3, 1, 4, 1, 2, 3, 4, 2]]

@[expose] def g2VGenA : Array (Array ℕ) := #[g2WGenA[0]!, g2SW (g2VWords.getD 0 []),
  g2SW (g2VWords.getD 1 [])]

@[expose] def g2VProd (e : ℕ) : Array ℕ :=
  compA 4060 (powA 4060 g2VGenA[0]! (e % 2)) (compA 4060 (powA 4060 g2VGenA[1]! (e / 2 % 2))
    (powA 4060 g2VGenA[2]! (e / 4 % 2)))

@[expose] def g2VArr : Array (Array ℕ) := Array.ofFn (n := 8) fun e => g2VProd e.val

@[expose] def g2InV (t : Array ℕ) : Bool := g2VArr.any fun u => eqA 4060 t u

@[expose] def g2NormV (t : Array ℕ) : Bool :=
  let ti := invCand 4060 t
  allLt 3 fun k => g2InV (compA 4060 (compA 4060 t g2VGenA[k]!) ti)

@[expose] def g2RhoWords : List (List ℤ) :=
  [[], [1], [2], [-1], [-2], [1, 1], [2, 1], [-2, 1], [1, 2], [2, 2], [-1, 2], [-1, -1], [1, -2],
    [-1, -2], [1, 2, 1], [2, 2, 1], [1, -2, 1], [-1, 2, 2], [1, 2, 2, 1], [-1, -1, 2, 2]]

@[expose] def g2RhoA (i : ℕ) : Array ℕ := ruCW (g2RhoWords.getD i [])

@[expose] def g2RhoCheck : Bool :=
  allLt 20 fun i => allLt 20 fun j => !decide (i < j) ||
    !g2NormW (compA 4060 (invCand 4060 (g2RhoA i)) (g2RhoA j))

@[expose] def g2NWords : List (List ℤ) := [[1, 2, 1, 1], [-1, -1, 2, -1]]

@[expose] def g2XWord : List ℤ :=
  [-1, -2, 1, 1, 1, 1, -2, 1, 2, 1, 1, 2, 1, 1, -2, -2, 1, 1, 2, -1, -1, 2, 2]

@[expose] def g2AWords : List (List ℤ) :=
  [[1, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1],
    [-1, -1, 2, -1, -1, -1, 2, -1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, -1, -1, 2, -1],
    [-1, -1, 2, -1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, -1, -1, 2, -1, -1, -1, 2, -1]]

@[expose] def g2AA (i : ℕ) : Array ℕ := ruCW (g2AWords.getD i [])

@[expose] def g2AProd (e : ℕ) : Array ℕ :=
  compA 4060 (powA 4060 (g2AA 0) (e % 2)) (compA 4060 (powA 4060 (g2AA 1) (e / 2 % 2))
    (powA 4060 (g2AA 2) (e / 4 % 2)))

@[expose] def g2CentW (t : Array ℕ) : Bool :=
  allLt 6 fun k => eqA 4060 (ruConjA t g2WGenA[k]!) g2WGenA[k]!

@[expose] def g2CentV (t : Array ℕ) : Bool :=
  allLt 3 fun k => eqA 4060 (ruConjA t g2VGenA[k]!) g2VGenA[k]!

@[expose] def g2SameW (t u : Array ℕ) : Bool :=
  allLt 6 fun k => eqA 4060 (ruConjA t g2WGenA[k]!) (ruConjA u g2WGenA[k]!)

@[expose] def g2NA (j : ℕ) : Array ℕ := ruCW (g2NWords.getD j [])

@[expose] def g2XA : Array ℕ := ruCW g2XWord

@[expose] def g2CommA (t u : Array ℕ) : Array ℕ := compA 4060 (ruConjA t u) (invCand 4060 u)

@[expose] def g2DIdx : List (ℕ × ℕ) := [(0, 1), (0, 2), (1, 1)]

@[expose] def g2DA (m : ℕ) : Array ℕ :=
  compA 4060 g2VGenA[(g2DIdx.getD m (0, 0)).2]!
    (ruConjA (invCand 4060 (g2NA (g2DIdx.getD m (0, 0)).1)) g2VGenA[(g2DIdx.getD m (0, 0)).2]!)

@[expose] def g2DProd (e : ℕ) : Array ℕ :=
  compA 4060 (powA 4060 (g2DA 0) (e % 2)) (compA 4060 (powA 4060 (g2DA 1) (e / 2 % 2))
    (powA 4060 (g2DA 2) (e / 4 % 2)))

end CFSG.Quasithin.H13.Ch4.G2Ru
