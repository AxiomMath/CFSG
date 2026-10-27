module

public import Certificates.Data.CFSGNative.ON.Certificate
public import Certificates.Data.CFSGNative.ONSchreier.Compact

public section

namespace CFSG.ONSchreier.Native

open CFSG.F3.Native CFSG.Sporadic.Fi23.Native CFSG.Sporadic.Th.Native CFSG.Sporadic.ON.Native

set_option compiler.extract_closed false

@[expose] def digitsW (s : String) : W :=
  ofV (V.ofFn 154 fun j => (s.toList.getD j '0').toNat - '0'.toNat)

@[expose] def vorbit (root : W) : VOrbit := orbitBFS colsA colsB root nPts

@[expose] def posOf (index : Std.HashMap W Nat) (d : Nat) : W → Nat := fun x => index.getD x d

@[expose] def discPar (m : Nat) (alpha beta : Table) : Array Nat := Id.run do
  let mut par : Array Nat := Array.replicate m m
  for q in [0:m] do
    let a := ap alpha q
    if a < m && par[a]! == m then par := par.set! a q
    let b := ap beta q
    if b < m && par[b]! == m then par := par.set! b q
  return par

@[expose] def discOK (m : Nat) (alpha beta : Table) (par : Array Nat) : Bool :=
  allIn 1 m fun k => decide (par[k]! < k) && (ap alpha par[k]! == k || ap beta par[k]! == k)

@[expose] def spanRows (O : VOrbit) (span : Array Nat) : Array W := span.map fun i => O.keys[i]!

@[expose] def basisOK (O : VOrbit) (span : Array Nat) (R : Array V) : Bool :=
  span.size == 154 && span.all (· < nPts) &&
    decide (mulW 154 ((transpose 154 R).map ofV) (spanRows O span) = idW 154)

@[expose] def formOK (M Minv : Array V) : Bool :=
  eqM 154 (transpose 154 M) M && Minv.size == 154 && wfM Minv &&
    eqM 154 (mul 154 Minv M) (idM 154) &&
    eqM 154 (mul 154 (mul 154 (transpose 154 rowsA) M) rowsA) M &&
    eqM 154 (mul 154 (mul 154 (transpose 154 rowsB) M) rowsB) M

@[expose] def gram (O : VOrbit) (span : Array Nat) (M : Array V) : Array V :=
  let U := toVM (spanRows O span)
  mul 154 (mul 154 U M) (transpose 154 U)

@[expose] def gramTree (G : Array V) : Array Nat × Array Nat := Id.run do
  let mut par : Array Nat := Array.replicate 154 0
  let mut dep : Array Nat := (Array.replicate 154 0).set! 0 1
  let mut q : Array Nat := #[0]
  for h in [0:154] do
    if h < q.size then
      let x := q[h]!
      for y in [0:154] do
        if y != x && G[x]!.get y != 0 && dep[y]! == 0 then
          par := par.set! y x
          dep := dep.set! y (dep[x]! + 1)
          q := q.push y
  return (par, dep)

@[expose] def gramConnOK (G : Array V) (par dep : Array Nat) : Bool :=
  dep[0]! == 1 &&
    allBelowN 154 fun y => y == 0 || (decide (par[y]! < 154) && par[y]! != y &&
      G[par[y]!]!.get y != 0 && decide (dep[par[y]!]! < dep[y]!) && decide (0 < dep[par[y]!]!))

@[expose] def sigRows (O : VOrbit) (M : Array V) (base : List Nat) : Array V :=
  Array.ofFn (n := 154) fun k =>
    if k.val < base.length then comb 154 M (O.keys[base[k.val]!]!).toV else V.zero

@[expose] def sigsOf (O : VOrbit) (T : Array W) : Array W :=
  Array.ofFn (n := nPts) fun i => mulVecT T O.keys[i.val]!

@[expose] def sigOK (S : Array W) (pos : W → Nat) : Bool :=
  S.size == nPts && allIn 0 nPts fun i => canon154 S[i]! && pos S[i]! == i

@[expose] def natTab (t : Table) : Array Nat := t.map (·.toNat)

@[expose] def strongArrs (n : Nat) (a0 a1 : Array Nat) (words : Array (List Int)) :
    Array (Array Nat) :=
  extendStrong n #[a0, a1] words

@[expose] def strongOK (n : Nat) (a0 a1 : Array Nat) (S : Array (Array Nat))
    (words : Array (List Int)) : Bool :=
  let Si := pinvs n S
  2 ≤ words.size && S.size == words.size && peq n S[0]! a0 && peq n S[1]! a1 &&
    allBelowN S.size (fun j => pisInv n S[j]! Si[j]!) &&
    allBelowN S.size (fun j => decide (j < 2) ||
      (plettersOK j words[j]! && peq n S[j]! (pword n S Si words[j]!)))

@[expose] def vectorCert (root : W) (span : Array Nat) (R M : Array V) (base : List Nat)
    (words : Array (List Int)) (chunks : Nat) : Bool :=
  let O := vorbit root
  let Minv := invV 154 M
  let pos := posOf (indexOf O.keys) nPts
  let G := gram O span M
  let tr := gramTree G
  let S := sigsOf O ((transpose 154 (sigRows O M base)).map ofV)
  let spos := posOf (indexOf S) nPts
  let a0 := natTab O.alpha
  let a1 := natTab O.beta
  orbitOK nPts colsA colsB O pos chunks && O.keys[0]! == root && !(root == W.zero) &&
    discOK nPts O.alpha O.beta (discPar nPts O.alpha O.beta) && basisOK O span R &&
    formOK M Minv &&
    gramConnOK G tr.1 tr.2 && base.length ≤ 154 && base.all (· < nPts) && sigOK S spos &&
    strongOK nPts a0 a1 (strongArrs nPts a0 a1 words) words

@[expose] def leadIsTwo (z : W) : Bool :=
  let v := z.toV
  match (List.range 154).find? (fun j => v.p.testBit j || v.m.testBit j) with
  | some j => v.m.testBit j
  | none => false

@[expose] def nuW (z : W) : W := if leadIsTwo z then z.neg else z

@[expose] def lineBFS (cA cB : Array W) (v₀ : W) (cap : Nat) : VOrbit := Id.run do
  let r := nuW v₀
  let mut keys : Array W := #[r]
  let mut index : Std.HashMap W Nat := (∅ : Std.HashMap W Nat).insert r 0
  let mut alpha : Table := #[]
  let mut beta : Table := #[]
  for h in [0:cap] do
    if h < keys.size then
      let x := keys[h]!
      let ya := nuW (mulVecT cA x)
      match index[ya]? with
      | some k => alpha := alpha.push (UInt32.ofNat k)
      | none =>
        index := index.insert ya keys.size
        alpha := alpha.push (UInt32.ofNat keys.size)
        keys := keys.push ya
      let yb := nuW (mulVecT cB x)
      match index[yb]? with
      | some k => beta := beta.push (UInt32.ofNat k)
      | none =>
        index := index.insert yb keys.size
        beta := beta.push (UInt32.ofNat keys.size)
        keys := keys.push yb
    else break
  return ⟨keys, alpha, beta⟩

@[inline, expose] def lineCheckAt (n : Nat) (U : VOrbit) (pos : W → Nat) (j : Nat) : Bool :=
  let x := U.keys[j]!
  canon154 x && pos x == j && nuW x == x && !(x == W.zero) &&
    ap U.alpha j < n && U.keys[ap U.alpha j]! == nuW (mulVecT colsA x) &&
    ap U.beta j < n && U.keys[ap U.beta j]! == nuW (mulVecT colsB x)

@[expose] def piTab (O : VOrbit) (posU : W → Nat) : Array Nat :=
  Array.ofFn (n := nPts) fun i => posU (nuW O.keys[i.val]!)

@[expose] def sigmaTab (O : VOrbit) (posL : W → Nat) : Array Nat :=
  Array.ofFn (n := nPts) fun i => posL O.keys[i.val]!.neg

@[expose] def piPre (n : Nat) (pi : Array Nat) : Array Nat := Id.run do
  let mut pre : Array Nat := Array.replicate n 0
  for i in [0:nPts] do
    pre := pre.set! pi[i]! i
  return pre

@[expose] def linesOK (n : Nat) (O U : VOrbit) (posU : W → Nat) (pi sigma pre : Array Nat)
    (chunks : Nat) : Bool :=
  U.keys.size == n && U.alpha.size == n && U.beta.size == n &&
    parAll n chunks (lineCheckAt n U posU) &&
    allIn 0 nPts (fun i => decide (pi[i]! < n) && U.keys[pi[i]!]! == nuW O.keys[i]! &&
      decide (sigma[i]! < nPts) && O.keys[sigma[i]!]! == O.keys[i]!.neg &&
      sigma[sigma[i]!]! == i && sigma[i]! != i && pi[sigma[i]!]! == pi[i]! &&
      pi[ap O.alpha i]! == ap U.alpha pi[i]! && pi[ap O.beta i]! == ap U.beta pi[i]!) &&
    allIn 0 n (fun j => decide (pre[j]! < nPts) && pi[pre[j]!]! == j)

@[expose] def lineCert (root : W) (n : Nat) (chunks : Nat) : Bool :=
  let O := vorbit root
  let posL := posOf (indexOf O.keys) nPts
  let U := lineBFS colsA colsB root n
  let posU := posOf (indexOf U.keys) n
  let pi := piTab O posU
  linesOK n O U posU pi (sigmaTab O posL) (piPre n pi) chunks && U.keys[0]! == nuW root &&
    discOK n U.alpha U.beta (discPar n U.alpha U.beta)

end CFSG.ONSchreier.Native
