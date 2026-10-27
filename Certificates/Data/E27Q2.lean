module

public import Certificates.Data.E27Table
public import Certificates.Data.E27Fus
public import Certificates.Data.CFSGNative.He.Fp

public section

namespace CFSG.HardMathSupport.Foote.E27

open CFSG.Sporadic.He.Native

@[expose] def transpM (d : Nat) (X : Array (Array Nat)) : Array (Array Nat) :=
  Array.ofFn (n := d) fun i => Array.ofFn (n := d) fun j => (X[j.val]!)[i.val]!

@[expose] def symJM (n : Nat) : Array (Array Nat) :=
  Array.ofFn (n := n + n) fun i => Array.ofFn (n := n + n) fun j =>
    if i.val + n = j.val ∨ j.val + n = i.val then 1 else 0

@[expose] def isSpM (n : Nat) (X : Array (Array Nat)) : Bool :=
  matEqB 2 (n + n) (mulM 2 (n + n) (mulM 2 (n + n) (transpM (n + n) X) (symJM n)) X) (symJM n)


@[expose] def polIso (d : Nat) (H X : Array (Array Nat)) : Bool :=
  let P := mulM 2 d (mulM 2 d (transpM d X) H) X
  (List.range d).all fun a => (P[a]!)[a]! % 2 == (H[a]!)[a]! % 2 &&
    (List.range d).all fun b =>
      ((P[a]!)[b]! + (P[b]!)[a]!) % 2 == ((H[a]!)[b]! + (H[b]!)[a]!) % 2

@[expose] def omGenOK (d : Nat) (H X G : Array (Array Nat)) : Bool :=
  polIso d H X && polIso d H G && matEqB 2 d (mulM 2 d G X) (mulM 2 d (mulM 2 d X X) G)

structure S0Data where
  n : Nat
  h : Nat
  m : Nat
  gensStr : String
  parStr : String
  LStr : String
  ksStr : String
  bsStr : String
  g3 : Nat × Nat × Nat := (0, 0, 0)

namespace S0Data

@[expose] def parseNats (s : String) : Array Nat :=
  (((s.replace "\n" " ").splitOn " ").filter fun t => !t.isEmpty).toArray.map String.toNat!

@[expose] def parseDigits (s : String) : Array Nat :=
  (s.toList.filter Char.isDigit).toArray.map fun c => c.toNat - '0'.toNat

@[expose] def pairsOf (a : Array Nat) : Array (Nat × Nat) :=
  Array.ofFn (n := a.size / 2) fun i => (a[2 * i.val]!, a[2 * i.val + 1]!)

@[expose, reducible] def d (D : S0Data) : Nat := D.h + D.h

@[expose] def par (D : S0Data) : Array (Nat × Nat) := pairsOf (parseNats D.parStr)

@[expose] def L (D : S0Data) : Array (Array Nat) :=
  let a := parseNats D.LStr
  Array.ofFn (n := D.m) fun j => Array.ofFn (n := D.n) fun i => a[j.val * D.n + i.val]!

@[expose] def matsOf (d cnt : Nat) (s : String) : Array (Array (Array Nat)) :=
  let a := parseDigits s
  Array.ofFn (n := cnt) fun t => Array.ofFn (n := d) fun i => Array.ofFn (n := d) fun j =>
    a[(t.val * d + i.val) * d + j.val]!

@[expose] def gensM (D : S0Data) : Array (Array (Array Nat)) := matsOf D.d D.m D.gensStr

@[expose] def eltsMat (d n : Nat) (gens : Array (Array (Array Nat))) (par : Array (Nat × Nat)) :
    Array (Array (Array Nat)) :=
  buildN #[idM d] (fun acc i => mulM 2 d (gens[(par[i]!).2]!) (acc[(par[i]!).1]!)) (n - 1)

@[expose] def baseOK (D : S0Data) : Bool :=
  let gens := D.gensM
  let par := D.par
  let L := D.L
  let elts := eltsMat D.d D.n gens par
  gens.size == D.m && par.size == D.n && L.size == D.m && decide (0 < D.n) &&
  (List.range D.n).all (fun i => i == 0 || ((par[i]!).1 < i && (par[i]!).2 < D.m)) &&
  (List.range D.m).all (fun j => isSpM D.h (gens[j]!) &&
    (List.range D.n).all fun i => (L[j]!)[i]! < D.n &&
      matEqB 2 D.d (mulM 2 D.d (gens[j]!) (elts[i]!)) (elts[(L[j]!)[i]!]!)) &&
  (List.range D.n).all fun i => (List.range i).all fun k => !matEqB 2 D.d (elts[i]!) (elts[k]!)

@[expose] def fusAllOK (D : S0Data) : Bool :=
  let gens := D.gensM
  let par := D.par
  let L := D.L
  let elts := eltsMat D.d D.n gens par
  let ks := matsOf D.d D.n D.ksStr
  let bs := parseNats D.bsStr
  (List.range D.n).all fun a => a == 0 || tabMul par L a (tabMul par L a a) != 0 ||
    (bs[a]! < D.n && isSpM D.h (ks[a]!) &&
      matEqB 2 D.d (mulM 2 D.d (ks[a]!) (elts[a]!)) (mulM 2 D.d (elts[bs[a]!]!) (ks[a]!)) &&
      decide (81 ≤ tabComm par L D.n bs[a]!))

@[expose] def gen3OK (D : S0Data) : Bool :=
  let gens := D.gensM
  let par := D.par
  let L := D.L
  let elts := eltsMat D.d D.n gens par
  let ks := matsOf D.d 3 D.ksStr
  let bs := parseNats D.bsStr
  let gl := [D.g3.1, D.g3.2.1, D.g3.2.2]
  decide (bigCount par L D.n = 27) && gl.all (fun a => decide (a < D.n) && isBig par L D.n a) &&
  monoOK par L D.g3.1 D.g3.2.1 D.g3.2.2 &&
  (List.range 3).all fun t =>
    decide (bs[t]! < D.n) && isSpM D.h (ks[t]!) &&
      matEqB 2 D.d (mulM 2 D.d (ks[t]!) (elts[gl[t]!]!)) (mulM 2 D.d (elts[bs[t]!]!) (ks[t]!)) &&
      decide (81 ≤ tabComm par L D.n bs[t]!)

end S0Data

end CFSG.HardMathSupport.Foote.E27

end
