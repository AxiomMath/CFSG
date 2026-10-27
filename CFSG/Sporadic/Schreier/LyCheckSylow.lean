module

public import CFSG.Sporadic.Schreier.LyCheckCover

public section

namespace CFSG.Sporadic.LySchreier.Native

open CFSG.Sporadic.Ly.Native CFSG.Sporadic.He.Native CFSG.Sporadic.Th.Native

set_option compiler.extract_closed false

@[expose] def sylowGens (cs : Array (Mat × Mat)) : Array Mat :=
  (Array.ofFn (n := 5) fun k =>
    evalWordM (fun i => (pairAt cs i).1) (fun i => (pairAt cs i).2) sylowWords[k.val]!).push matA

@[expose] def sylowBFS (us : Array Mat) (cap : Nat) :
    Array Mat × Array Nat × Array Nat × Array (Array Nat) := Id.run do
  let mut index : Std.HashMap Mat Nat := (∅ : Std.HashMap _ _).insert (idM 111) 0
  let mut pts : Array Mat := #[idM 111]
  let mut par : Array Nat := #[0]
  let mut lab : Array Nat := #[0]
  let mut lam : Array (Array Nat) := Array.replicate us.size #[]
  for h in [0:cap] do
    if h < pts.size then
      let x := pts[h]!
      for k in [0:us.size] do
        let y := mulM 5 111 us[k]! x
        match index[y]? with
        | some j => lam := lam.set! k (lam[k]!.push j)
        | none =>
          index := index.insert y pts.size
          lam := lam.set! k (lam[k]!.push pts.size)
          pts := pts.push y
          par := par.push h
          lab := lab.push k
  return (pts, par, lab, lam)

@[inline, expose] def sylowPos (par lab : Array Nat) (j : Nat) : Nat := 6 * par[j]! + lab[j]!

@[expose] def sylowEnumOK (us : Array Mat) (n : Nat)
    (B : Array Mat × Array Nat × Array Nat × Array (Array Nat)) : Bool :=
  let pts := B.1
  let par := B.2.1
  let lab := B.2.2.1
  let lam := B.2.2.2
  let index : Std.HashMap Mat Nat := (List.range pts.size).foldl (fun m k => m.insert pts[k]! k) ∅
  us.size == 6 && pts.size == n && par.size == n && lab.size == n && lam.size == 6 &&
    (lam.all fun t => t.size == n && t.all (· < n)) && pts[0]! == idM 111 &&
    allIn 0 n (fun k => index.getD pts[k]! n == k) &&
    allIn 0 n (fun i => allIn 0 6 fun k => mulM 5 111 us[k]! pts[i]! == pts[lam[k]![i]!]!) &&
    allIn 1 n (fun j => par[j]! < j && lab[j]! < 6 && lam[lab[j]!]![par[j]!]! == j) &&
    allIn 1 (n - 1) (fun j => sylowPos par lab j < sylowPos par lab (j + 1)) &&
    allIn 0 n (fun i => allIn 0 6 fun k =>
      lam[k]![i]! == 0 || sylowPos par lab lam[k]![i]! ≤ 6 * i + k)

@[expose] def mulTabOf (n : Nat) (par lab : Array Nat) (lam : Array (Array Nat)) :
    Array (Array Nat) := Id.run do
  let mut T : Array (Array Nat) := #[Array.ofFn (n := n) fun j => j.val]
  for i in [1:n] do
    let row := T[par[i]!]!
    T := T.push (row.map fun x => lam[lab[i]!]![x]!)
  return T

@[expose] def mulTabOK (T : Array (Array Nat)) (n : Nat) (par lab : Array Nat)
    (lam : Array (Array Nat)) : Bool :=
  T.size == n && (T.all fun r => r.size == n && r.all (· < n)) &&
    allIn 0 n (fun j => T[0]![j]! == j) &&
    allIn 1 n (fun i => allIn 0 n fun j => T[i]![j]! == lam[lab[i]!]![T[par[i]!]![j]!]!)

@[inline, expose] def tm (T : Array (Array Nat)) (i j : Nat) : Nat := T[i]![j]!

@[expose] def tinv (T : Array (Array Nat)) (n i : Nat) : Nat :=
  ((List.range n).find? fun j => tm T i j == 0).getD 0

@[expose] def tcomm (T : Array (Array Nat)) (n i j : Nat) : Nat :=
  tm T (tm T (tm T i j) (tinv T n i)) (tinv T n j)

@[expose] def tpow (T : Array (Array Nat)) (i : Nat) : Nat → Nat
  | 0 => 0
  | e + 1 => tm T (tpow T i e) i

@[expose] def closedOK (T : Array (Array Nat)) (L : List Nat) : Bool :=
  L.all fun a => L.all fun b => L.contains (tm T a b)

@[inline, expose] def isInv (T : Array (Array Nat)) (x : Nat) : Bool := x != 0 && tm T x x == 0

@[expose] def spanBy (T : Array (Array Nat)) (E : List Nat) (x : Nat) : List Nat :=
  (E ++ E.map (tm T x ·)).mergeSort (· ≤ ·)

@[expose] def extendsBy (T : Array (Array Nat)) (E : List Nat) (x : Nat) : Bool :=
  isInv T x && !E.contains x && E.all fun e => tm T x e == tm T e x

@[expose] def nextEA (T : Array (Array Nat)) (n : Nat) (L : List (List Nat)) : List (List Nat) :=
  (L.flatMap fun E => ((List.range n).filter (extendsBy T E)).map (spanBy T E)).eraseDups

@[expose] def extOK (T : Array (Array Nat)) (n : Nat) (L L' : List (List Nat)) : Bool :=
  L.all fun E => (List.range n).all fun x => !extendsBy T E x || L'.contains (spanBy T E x)

@[expose] def ord8Mod (T : Array (Array Nat)) (Z : List Nat) (i : Nat) : Bool :=
  Z.contains (tpow T i 8) && !Z.contains (tpow T i 4)

@[expose] def derivedTree (T : Array (Array Nat)) (n : Nat) :
    Array Nat × Array Nat × Array Nat × Array Nat := Id.run do
  let comms : Array (Nat × Nat × Nat) := Id.run do
    let mut cs : Array (Nat × Nat × Nat) := #[]
    for a in [0:n] do
      for b in [0:n] do
        let c := tcomm T n a b
        if !(cs.any fun t => t.1 == c) then cs := cs.push (c, a, b)
    return cs
  let mut D : Array Nat := #[0]
  let mut dPar : Array Nat := #[0]
  let mut dA : Array Nat := #[0]
  let mut dB : Array Nat := #[0]
  for h in [0:n] do
    if h < D.size then
      for t in comms do
        let y := tm T t.1 D[h]!
        if !D.contains y then
          D := D.push y
          dPar := dPar.push h
          dA := dA.push t.2.1
          dB := dB.push t.2.2
  return (D, dPar, dA, dB)

@[expose] def tableOK (T : Array (Array Nat)) (n : Nat) (D dPar dA dB : Array Nat)
    (L1 L2 L3 L4 : List (List Nat)) (i0 : Nat) : Bool :=
  let Z : List Nat := [0, 6]
  let Dl := D.toList
  let Q := qIndices.toList
  let ZQ : List Nat := [0, 6, 113, 207]
  allIn 0 n (fun i => tinv T n i < n && tm T i (tinv T n i) == 0) &&
  allIn 0 n (fun i => (allIn 0 n fun j => tm T i j == tm T j i) == Z.contains i) &&
  D.size == 32 && D[0]! == 0 && Dl.Nodup && closedOK T Dl && Dl.contains 0 && Dl.contains 6 &&
    allIn 0 n (fun a => allIn 0 n fun b => Dl.contains (tcomm T n a b)) &&
    dPar.size == 32 && dA.size == 32 && dB.size == 32 &&
    allIn 1 32 (fun k => dPar[k]! < k && dA[k]! < n && dB[k]! < n &&
      tm T (tcomm T n dA[k]! dB[k]!) D[dPar[k]!]! == D[k]!) &&
    allIn 0 n (fun i => Dl.contains (tm T i i)) && (Dl.all (· < n)) &&
    (Dl.all fun d => Dl.contains (tinv T n d)) &&
    extOK T n [[0]] L1 && extOK T n L1 L2 && extOK T n L2 L3 && extOK T n L3 L4 &&
    L4 == [e16[0]!.toList, e16[1]!.toList] &&
    (L4.all fun E => (List.range n).all fun x => !extendsBy T E x) &&
    (L4.all fun E => closedOK T E && E.contains 0 && E.all fun x => x == 0 || isInv T x) &&
    (L4.all fun E => E.all fun a => E.all fun b => tm T a b == tm T b a) &&
    (L4.all fun E => E.length == 16 && E.Nodup && E.all (· < n)) &&
    Q.length == 64 && Q.Nodup && Q.all (· < n) && closedOK T Q && Q.contains 0 &&
    (Q.all fun q => Q.contains (tinv T n q)) &&
    (Q.all fun q => L4[0]!.any fun a => L4[1]!.any fun b => tm T a b == q) &&
    (L4.all fun E => E.all fun x => Q.contains x) &&
    (Q.all fun q => (Q.all fun r => tm T q r == tm T r q) == ZQ.contains q) &&
    (ZQ.all fun q => Q.contains q && tm T q q == 0) && Q.contains fIndex &&
    i0 < n && !Dl.contains i0 && (Dl.all fun d => ord8Mod T Z (tm T i0 d)) &&
    allIn 0 n (fun i => Dl.contains i || !(Dl.all fun d => ord8Mod T Z (tm T i d)) ||
      Dl.contains (tm T (tinv T n i0) i))

@[expose] def invConjugators : List (Nat × List Int) :=
  ((involutionConjugatorsTxt.splitOn "\n").filter (· != "")).map fun line =>
    match line.splitOn " : " with
    | [k, w] => (k.toNat!, parseInts w)
    | _ => (0, [])

@[expose] def qWords : List (Nat × List Int) :=
  [(155, [3, 1, 3, 2, 1]), (101, [1, 3, 4, 1]), (49, [4, 3, 2]), (18, [2, 3])]

@[expose] def localOK (b4 : Mat) (cs : Array (Mat × Mat)) (us : Array Mat)
    (T : Array (Array Nat)) (pts : Array Mat) : Bool :=
  let f := pts[fIndex]!
  let h := (pairAt cs 11).2
  let w := evalWordM seedM (seedMInv b4) fusionWord
  let wi := invM 5 111 w
  let x := mulM 5 111 (mulM 5 111 w matA) wi
  let zx := mulM 5 111 matA x
  let xf := mulM 5 111 x f
  let g := mulM 5 111 (powM 5 111 xf 7) (powM 5 111 zx 4)
  (invConjugators.map (·.1)) == (List.range 256).filter (fun i => isInv T i && i != 6) &&
    (invConjugators.all fun e =>
      let W := evalWordM (fun i => (pairAt cs i).1) (fun i => (pairAt cs i).2) e.2
      mulM 5 111 W f == mulM 5 111 pts[e.1]! W) &&
    mulM 5 111 h (mulM 5 111 h h) == idM 111 && diffMod5 h (idM 111) &&
    (qIndices.all fun q => mulM 5 111 h pts[q]! == mulM 5 111 pts[q]! h) &&
    mulM 5 111 w wi == idM 111 && powM 5 111 zx 9 == idM 111 && powM 5 111 xf 15 == idM 111 &&
    mulM 5 111 g matA == mulM 5 111 f g &&
    (qWords.all fun e => evalWordM (fun k => us[k]!) (fun k => us[k]!) e.2 == pts[e.1]!)

@[expose] def sylowCertificate (_ : Unit) : Bool :=
  let b4 := powM 5 111 matB 4
  let cs := cStarArr b4
  let us := sylowGens cs
  let B := sylowBFS us 256
  let T := mulTabOf 256 B.2.1 B.2.2.1 B.2.2.2
  let DT := derivedTree T 256
  let L1 := nextEA T 256 [[0]]
  let L2 := nextEA T 256 L1
  let L3 := nextEA T 256 L2
  let L4 := nextEA T 256 L3
  mulM 5 111 matB b4 == idM 111 && invPairsOK cs && sylowEnumOK us 256 B &&
    B.1[6]! == matA && mulTabOK T 256 B.2.1 B.2.2.1 B.2.2.2 &&
    tableOK T 256 DT.1 DT.2.1 DT.2.2.1 DT.2.2.2 L1 L2 L3 L4 38 &&
    localOK b4 cs us T B.1

end CFSG.Sporadic.LySchreier.Native
