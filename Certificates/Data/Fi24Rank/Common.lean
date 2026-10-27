module

public import Certificates.Data.CFSGNative.MonsterB.Co2Chain

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1017.Fi24RankNative

open CFSG.Monster.B.Co2.Native

set_option compiler.extract_closed false

@[expose] def hexVal (c : Char) : Nat :=
  if c.isDigit then c.toNat - 48 else if 'a' ≤ c ∧ c ≤ 'f' then c.toNat - 87 else 16

@[expose] def hexNums (d : Nat) (s : String) : Array Nat :=
  (s.foldl (fun (acc : Array Nat × Nat × Nat) c =>
    let v := hexVal c
    if v < 16 then
      if acc.2.2 + 1 = d then (acc.1.push (acc.2.1 * 16 + v), 0, 0)
      else (acc.1, acc.2.1 * 16 + v, acc.2.2 + 1)
    else acc) (#[], 0, 0)).1

@[expose] def rowsOf (m : Nat) (a : Array Nat) : Array (Array Nat) :=
  Array.ofFn (n := a.size / m) fun i => a.extract (i.val * m) (i.val * m + m)

@[inline, expose] def anyLt (n : Nat) (p : Nat → Bool) : Bool := !(allLt n fun i => !p i)

@[expose] def powA (n : Nat) (t : Array Nat) : Nat → Array Nat
  | 0 => idA n
  | e + 1 => compA n t (powA n t e)

@[inline, expose] def dig (i k : Nat) : Nat := i / 3 ^ k % 3

@[expose] def iotaA (n : Nat) (A : Array (Array Nat)) (i : Nat) : Array Nat :=
  compA n (powA n A[0]! (dig i 0)) (compA n (powA n A[1]! (dig i 1))
    (compA n (powA n A[2]! (dig i 2)) (compA n (powA n A[3]! (dig i 3)) (powA n A[4]! (dig i 4)))))

@[expose] def addD (i j : Nat) : Nat :=
  (dig i 0 + dig j 0) % 3 + 3 * ((dig i 1 + dig j 1) % 3) + 9 * ((dig i 2 + dig j 2) % 3) +
    27 * ((dig i 3 + dig j 3) % 3) + 81 * ((dig i 4 + dig j 4) % 3)

@[expose] def negD (i : Nat) : Nat :=
  (3 - dig i 0) % 3 + 3 * ((3 - dig i 1) % 3) + 9 * ((3 - dig i 2) % 3) +
    27 * ((3 - dig i 3) % 3) + 81 * ((3 - dig i 4) % 3)

@[expose] def iotas (n : Nat) (A : Array (Array Nat)) : Array (Array Nat) :=
  Array.ofFn (n := 243) fun i => iotaA n A i.val

@[expose] def pbBFS (mus : Array (Array Nat)) : Array (Array Nat) × Array Nat × Array Nat := Id.run do
  let mut L : Array (Array Nat) := #[idA 243]
  let mut par : Array Nat := #[0]
  let mut lab : Array Nat := #[0]
  let mut q := 0
  for _ in [0:243] do
    if q < L.size then
      for l in [0:mus.size] do
        let x := compA 243 L[q]! mus[l]!
        if !(L.any fun y => eqA 243 x y) then
          L := L.push x
          par := par.push q
          lab := lab.push l
      q := q + 1
  return (L, par, lab)

@[expose] def permsOK (n : Nat) (A G mus : Array (Array Nat)) : Bool :=
  A.size == 5 && G.size == 2 && mus.size == 2 &&
    allLt 5 (fun k => isInvA n A[k]! (invCand n A[k]!)) &&
    allLt 2 (fun l => isInvA n G[l]! (invCand n G[l]!)) &&
    allLt 2 (fun l => isInvA 243 mus[l]! (invCand 243 mus[l]!))

@[expose] def multOK (n : Nat) (A : Array (Array Nat)) : Bool :=
  allLt 5 (fun k => allLt 5 fun l => eqA n (compA n A[k]! A[l]!) (compA n A[l]! A[k]!)) &&
    allLt 5 (fun k => eqA n (powA n A[k]! 3) (idA n))

@[expose] def injOK (I : Array (Array Nat)) (p₀ : Nat) : Bool :=
  allLt 243 fun i => allLt 243 fun j => i == j || I[i]![p₀]! != I[j]![p₀]!

@[expose] def conjOK (n : Nat) (I G mus : Array (Array Nat)) : Bool :=
  allLt 2 fun l => allLt 243 fun i =>
    decide (mus[l]![i]! < 243) &&
      eqA n (compA n G[l]! (compA n I[i]! (invCand n G[l]!))) I[mus[l]![i]!]!

@[expose] def pbOK (mus : Array (Array Nat)) (sz : Nat) : Bool :=
  let B := pbBFS mus
  let L := B.1
  let par := B.2.1
  let lab := B.2.2
  L.size == sz && eqA 243 L[0]! (idA 243) &&
    allLt sz (fun k => isInvA 243 L[k]! (invCand 243 L[k]!)) &&
    allLt sz (fun k => k == 0 || (decide (par[k]! < k) && decide (lab[k]! < 2) &&
      eqA 243 L[k]! (compA 243 L[par[k]!]! mus[lab[k]!]!))) &&
    allLt 2 (fun l => anyLt sz fun r => eqA 243 mus[l]! L[r]!) &&
    allLt sz (fun k => allLt sz fun l =>
      let c := compA 243 L[k]! L[l]!
      anyLt sz fun r => eqA 243 c L[r]!) &&
    allLt sz (fun k => anyLt sz fun r => eqA 243 (compA 243 L[k]! L[r]!) (idA 243)) &&
    allLt sz (fun k => allLt sz fun l => k == l || !eqA 243 L[k]! L[l]!)

@[expose] def fix1 (t : Array Nat) : Nat := (List.finRange 243).countP fun v => t[v.val]! == v.val

@[expose] def fix2 (t u : Array Nat) : Nat :=
  (List.finRange 243).countP fun v => t[v.val]! == v.val && u[v.val]! == v.val

@[expose] def fix3 (t u w : Array Nat) : Nat :=
  (List.finRange 243).countP fun v =>
    t[v.val]! == v.val && u[v.val]! == v.val && w[v.val]! == v.val

@[inline, expose] def commA (t u : Array Nat) : Bool := eqA 243 (compA 243 t u) (compA 243 u t)

@[inline, expose] def pairEx (x y : Array Nat) : Bool :=
  eqA 243 x (idA 243) || !commA x y || eqA 243 y (idA 243) || eqA 243 y x ||
    eqA 243 y (compA 243 x x)

@[expose] def fixOK (mus : Array (Array Nat)) (sz : Nat) : Bool :=
  let L := (pbBFS mus).1
  let e := idA 243
  allLt sz (fun k => eqA 243 L[k]! e || decide (fix1 L[k]! ≤ 27)) &&
    allLt sz (fun k => allLt sz fun l => pairEx L[k]! L[l]! || decide (fix2 L[k]! L[l]! ≤ 9)) &&
    allLt sz (fun k => allLt sz fun l => pairEx L[k]! L[l]! || allLt sz fun r =>
      !commA L[k]! L[r]! || !commA L[l]! L[r]! ||
      (anyLt 3 fun i => anyLt 3 fun j =>
        eqA 243 L[r]! (compA 243 (powA 243 L[k]! i) (powA 243 L[l]! j))) ||
      decide (fix3 L[k]! L[l]! L[r]! ≤ 3))

@[expose] def nonabOK (mus : Array (Array Nat)) (sz : Nat) : Bool :=
  let L := (pbBFS mus).1
  anyLt sz fun k => anyLt sz fun l => !commA L[k]! L[l]!

@[expose] def stabList (I : Array (Array Nat)) (p : Nat) : List Nat :=
  (List.range 243).filter fun i => I[i]![p]! == p

@[expose] def uniqAt (n : Nat) (I : Array (Array Nat)) (S : Array (List Nat)) (p : Nat) : Bool :=
  (allLt n fun q => S[q]! != S[p]! || anyLt 243 fun i => I[i]![p]! == q) &&
    allLt 243 fun i => I[i]![I[i]![p]!]! != p || I[i]![p]! == p

@[expose] def stabs (n : Nat) (I : Array (Array Nat)) : Array (List Nat) :=
  Array.ofFn (n := n) fun p => stabList I p.val

@[expose] def sideOK (n : Nat) (A G mus : Array (Array Nat)) (p₀ sz : Nat) : Bool :=
  let I := iotas n A
  permsOK n A G mus && decide (p₀ < n) && multOK n A && injOK I p₀ && conjOK n I G mus &&
    pbOK mus sz && fixOK mus sz

end CFSG.LocalAnalysis.GLTheoremA.H1017.Fi24RankNative
