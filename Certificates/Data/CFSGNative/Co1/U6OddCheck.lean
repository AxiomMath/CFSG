module

public import Certificates.Data.CFSGNative.Co1.CoTwoChain

public section

namespace CFSG.Sporadic.Co1.U6OddNative

open CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Th.Native CFSG.Sporadic.Co1.OddNative
  CFSG.Sporadic.Co1.CoTwoNative

@[expose] def xcN : List Nat → Nat → Nat
  | [], _ => 0
  | x :: xs, m => (if m % 2 = 1 then x else 0) ^^^ xcN xs (m / 2)

@[expose] def sigN (L : Nat → Nat) (c : List Nat) : List Nat :=
  (List.range (2 ^ c.length)).map fun m => L (xcN c m)

@[expose] def clsKey (L : Nat → Nat) (u₁ u₂ v : Nat) : List Nat :=
  [L v, L (u₁ ^^^ v), L (u₂ ^^^ v), L (u₁ ^^^ (u₂ ^^^ v))]

@[expose] def classN (L : Nat → Nat) (Wl : List Nat) (u₁ u₂ bi : Nat) : List Nat :=
  Wl.filter fun v => clsKey L u₁ u₂ v == clsKey L u₁ u₂ bi

@[expose] def sectionsN : List (List Nat) → List (List Nat)
  | [] => [[]]
  | l :: ls => l.flatMap fun x => (sectionsN ls).map (x :: ·)

@[expose] def tuplesN (L : Nat → Nat) (Wl : List Nat) : List Nat → List (List Nat)
  | u₁ :: u₂ :: rest =>
    (sectionsN ([u₁] :: [u₂] :: rest.map (classN L Wl u₁ u₂))).filter fun c =>
      sigN L c == sigN L (u₁ :: u₂ :: rest)
  | _ => []

structure PrimeData where
  p : Nat
  g : Nat
  base : List Nat
  lv : List (List Nat)
  sz : List Nat
  final : List Nat
  b : List Nat
  t : Nat
  k : Nat

@[expose] def fixAll (rr : Nat → Array Nat) (xs ss : List Nat) : Bool :=
  ss.all fun s => xs.all fun x => fixOK rr x s

@[expose] def chainCheck (rr : Nat → Array Nat) (u₁ u₂ : Nat) (pd : PrimeData) : Bool :=
  decide (pd.lv.length = pd.base.length) && decide (pd.sz.length = pd.base.length) &&
    (List.range pd.base.length).all (fun i =>
      fixAll rr (u₁ :: u₂ :: pd.base.take i) (pd.lv.getD i []) &&
        decide (pd.sz.getD i 0 ≤ treeSize rr (pd.lv.getD i []) (pd.base.getD i 0))) &&
    fixAll rr (u₁ :: u₂ :: pd.base) pd.final &&
      decide (9196830720 ≤ ((List.range pd.base.length).map fun i => pd.sz.getD i 0).prod * pd.k)

@[expose] def gCheck (rr : Nat → Array Nat) (u₁ u₂ : Nat) (pd : PrimeData) : Bool :=
  validRows (rr pd.g) && decide (orderN (rr pd.g) = pd.p) &&
    fixAll rr (u₁ :: u₂ :: pd.base) [pd.g]

@[expose] def fixedOfG (rr : Nat → Array Nat) (g : Nat) : List Nat :=
  fixList [transposeRows 24 (rr g)]

@[expose] def tupleCheck (rr : Nat → Array Nat) (L : Nat → Nat) (u₁ u₂ : Nat)
    (pd : PrimeData) : Bool :=
  let Wl := fixedOfG rr pd.g
  let tbl : List (Nat × Nat) := Wl.map fun w => (w, L w)
  decide (pd.b.take (2 + pd.base.length) = u₁ :: u₂ :: pd.base) &&
    pd.b.all (fun x => Wl.contains x) &&
    decide ((tuplesN (fun w => (tbl.lookup w).getD 0) Wl pd.b).length ≤ pd.t)

@[expose] def invPair (P Q : Array Nat) : Bool := mulRows 24 P Q == idRows 24

@[expose] def classCheck (rr : Nat → Array Nat) (u₁ u₂ : Nat) (pd : PrimeData) (cl : List Nat)
    (n : Nat) : Bool :=
  let P := (cl.map rr).toArray
  let Q := (cl.map fun c => powRows 24 (rr c) (orderN (rr c) - 1)).toArray
  let F := forestBFS P Q #[rr pd.g] n
  fixAll rr (u₁ :: u₂ :: pd.base) cl && (List.range P.size).all (fun l => invPair P[l]! Q[l]!) &&
    forestOK P Q #[rr pd.g] F && decide (n ≤ F.pts.size)

@[expose] def normalizesG (rr : Nat → Array Nat) (p g x : Nat) : Bool :=
  (List.range (p - 1)).any fun j =>
    mulRows 24 (rr x) (rr g) == mulRows 24 (powRows 24 (rr g) (j + 1)) (rr x)

@[expose] def normCheck (rr : Nat → Array Nat) (u₁ u₂ : Nat) (pd : PrimeData) (xs : List Nat)
    (n : Nat) : Bool :=
  let P := (xs.map rr).toArray
  let Q := Array.replicate xs.length (idRows 24)
  let F := forestBFS P Q #[idRows 24] n
  fixAll rr [u₁, u₂] xs && xs.all (normalizesG rr pd.p pd.g) &&
    forestOK P Q #[idRows 24] F && decide (n ≤ F.pts.size) &&
    (List.range P.size).all (fun l => Q[l]! == idRows 24)

@[expose] def commCount (pts : Array (Array Nat)) (x : Array Nat) : Nat :=
  countBelow (fun j => mulRows 24 x pts[j]! == mulRows 24 pts[j]! x) pts.size 0

@[expose] def bigList (pts : Array (Array Nat)) : List (Array Nat) :=
  pts.toList.filter fun x => decide (243 ≤ commCount pts x)

@[expose] def closedMul (pts : Array (Array Nat)) : Bool :=
  let hs : Std.HashSet (Array Nat) := Std.HashSet.ofList pts.toList
  pts.all (fun x => pts.all fun y => hs.contains (mulRows 24 x y)) &&
    pts.all (fun x => invPair x (powRows 24 x (orderN x - 1)) &&
      hs.contains (powRows 24 x (orderN x - 1)))

@[expose] def s0Check (rr : Nat → Array Nat) (u₁ u₂ : Nat) (gens : List Nat) : Bool :=
  let P := (gens.map rr).toArray
  let Q := Array.replicate gens.length (idRows 24)
  let F := forestBFS P Q #[idRows 24] 729
  fixAll rr [u₁, u₂] gens && forestOK P Q #[idRows 24] F && decide (F.pts.size = 729) &&
    (List.range P.size).all (fun l => Q[l]! == idRows 24) &&
    F.pts.all (fun R => isFixedN (transposeRows 24 R) u₁ && isFixedN (transposeRows 24 R) u₂) &&
    closedMul F.pts && decide ((bigList F.pts).length ≤ 27)

end CFSG.Sporadic.Co1.U6OddNative
