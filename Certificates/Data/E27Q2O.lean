module

public import Certificates.Data.E27Q2

public section

namespace CFSG.HardMathSupport.Foote.E27

open CFSG.Sporadic.He.Native

@[expose] def HPform (n : Nat) : Array (Array Nat) :=
  Array.ofFn (n := n + n) fun i => Array.ofFn (n := n + n) fun j =>
    if i.val + n = j.val then 1 else 0

@[expose] def HMform (n : Nat) : Array (Array Nat) :=
  Array.ofFn (n := n + n) fun i => Array.ofFn (n := n + n) fun j =>
    if (i.val < n - 1 ∧ i.val + (n - 1) = j.val) ∨
        (i.val = 2 * (n - 1) ∧ (j.val = 2 * (n - 1) ∨ j.val = 2 * (n - 1) + 1)) ∨
        (i.val = 2 * (n - 1) + 1 ∧ j.val = 2 * (n - 1) + 1) then 1 else 0

structure S0DataO where
  base : S0Data
  kind : Nat
  ginvStr : String

namespace S0DataO

@[expose] def hMat (D : S0DataO) : Array (Array Nat) :=
  if D.kind = 0 then HPform D.base.h else HMform D.base.h

@[expose] def ginvM (D : S0DataO) : Array (Array (Array Nat)) :=
  S0Data.matsOf D.base.d D.base.m D.ginvStr

@[expose] def baseOK (D : S0DataO) : Bool :=
  let B := D.base
  let gens := B.gensM
  let gi := D.ginvM
  let H := D.hMat
  let par := B.par
  let L := B.L
  let elts := S0Data.eltsMat B.d B.n gens par
  gens.size == B.m && gi.size == B.m && par.size == B.n && L.size == B.m && decide (0 < B.n) &&
  (List.range B.n).all (fun i => i == 0 || ((par[i]!).1 < i && (par[i]!).2 < B.m)) &&
  (List.range B.m).all (fun j => omGenOK B.d H (gens[j]!) (gi[j]!) &&
    (List.range B.n).all fun i => (L[j]!)[i]! < B.n &&
      matEqB 2 B.d (mulM 2 B.d (gens[j]!) (elts[i]!)) (elts[(L[j]!)[i]!]!)) &&
  (List.range B.n).all fun i => (List.range i).all fun k => !matEqB 2 B.d (elts[i]!) (elts[k]!)

@[expose] def fusAllOK (D : S0DataO) : Bool :=
  let B := D.base
  let gens := B.gensM
  let H := D.hMat
  let par := B.par
  let L := B.L
  let elts := S0Data.eltsMat B.d B.n gens par
  let ks := S0Data.matsOf B.d B.n B.ksStr
  let bs := S0Data.parseNats B.bsStr
  (List.range B.n).all fun a => a == 0 || tabMul par L a (tabMul par L a a) != 0 ||
    (bs[a]! < B.n && polIso B.d H (ks[a]!) &&
      matEqB 2 B.d (mulM 2 B.d (ks[a]!) (elts[a]!)) (mulM 2 B.d (elts[bs[a]!]!) (ks[a]!)) &&
      decide (81 ≤ tabComm par L B.n bs[a]!))

@[expose] def gen3OK (D : S0DataO) : Bool :=
  let B := D.base
  let gens := B.gensM
  let H := D.hMat
  let par := B.par
  let L := B.L
  let elts := S0Data.eltsMat B.d B.n gens par
  let ks := S0Data.matsOf B.d 3 B.ksStr
  let bs := S0Data.parseNats B.bsStr
  let gl := [B.g3.1, B.g3.2.1, B.g3.2.2]
  decide (bigCount par L B.n = 27) && gl.all (fun a => decide (a < B.n) && isBig par L B.n a) &&
  monoOK par L B.g3.1 B.g3.2.1 B.g3.2.2 &&
  (List.range 3).all fun t =>
    decide (bs[t]! < B.n) && polIso B.d H (ks[t]!) &&
      matEqB 2 B.d (mulM 2 B.d (ks[t]!) (elts[gl[t]!]!)) (mulM 2 B.d (elts[bs[t]!]!) (ks[t]!)) &&
      decide (81 ≤ tabComm par L B.n bs[t]!)

end S0DataO

end CFSG.HardMathSupport.Foote.E27

end
