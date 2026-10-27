
module

public import CFSG.Sporadic.FischerOddCore.FischerOuterFi22Data
public import CFSG.Sporadic.FischerOddCore.Fi24R2KCheckBase
public import CFSG.Sporadic.FischerOddCore.Fi22Cent
public meta import CFSG.Sporadic.FischerOddCore.FischerOuterFi22Data
public meta import CFSG.Sporadic.FischerOddCore.Fi24R2KCheckBase
public meta import CFSG.Sporadic.FischerOddCore.Fi22Cent
public meta import CFSG.Sporadic.FischerOddCore.Fi22Ext
public import CFSG.Sporadic.FischerOddCore.Fi22Ext

public section

namespace CFSG.Sporadic.FischerOddCore

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

@[expose] def strongOf (n : Nat) (O : Array (Array Nat)) (W : Array (List Int)) :
    Array (Array Nat) :=
  (List.range W.size).foldl (fun S j =>
    if j < O.size then S.push O[j]! else S.push (wordA n S (rawInvs n S) W[j]!)) #[]

@[expose] def treeConjN (n r : Nat) (gens : Array (Array Nat)) (s₀ tree : Array Nat) :
    Array (Array Nat) :=
  tree.foldl (fun acc t => acc.push (conjA n gens[t % r]! acc[t / r]!)) #[s₀]

@[expose] def powA (n : Nat) (t : Array Nat) : Nat → Array Nat
  | 0 => idA n
  | e + 1 => compA n t (powA n t e)

@[expose] def fo22N3Strong : Array (Array Nat) := strongOf 3510 #[fo22A3, fo22B3] fo22N3Words

@[expose] def fo22P3Strong : Array (Array Nat) := strongOf 1575 #[fo22Pa3, fo22Pb3] fo22P3Words

@[expose] def fo22N4Strong : Array (Array Nat) := strongOf 3510 #[fo22A4, fo22B4] fo22N4Words

@[expose] def fo22P4Strong : Array (Array Nat) := strongOf 63 #[fo22Pa4, fo22Pb4] fo22P4Words

@[expose] def fo22P2Strong : Array (Array Nat) := strongOf 27 (rowsOf 27 fo22P2Flat) fo22P2Words

@[expose] def fo22HBase : Array Nat := #[0, 1, 2, 3, 6, 4]

@[noinline, expose] def fo22ChainOK (n : Nat) (S : Array (Array Nat)) (base : Array Nat)
    (W : Array (List Int)) (k size ord : Nat) : Bool :=
  S.size == size && rawChainOK n (S.extract 0 k) S base W 4 &&
    (rawOrbitSizes n S base).prod == ord

@[noinline, expose] def fo22InNormalOK (S : Array (Array Nat)) (base : Array Nat)
    (Sh hgens : Array (Array Nat)) : Bool :=
  let lvN := rawLevels 3510 S base
  let lvH := rawLevels 3510 Sh fo22HBase
  siftA 3510 lvH fo22HBase 0 S[0]! && siftA 3510 lvH fo22HBase 0 S[1]! &&
    allLt hgens.size (fun j => siftA 3510 lvN base 0 (conjA 3510 hgens[j]! S[0]!) &&
      siftA 3510 lvN base 0 (conjA 3510 hgens[j]! S[1]!))

@[noinline, expose] def fo22ClassOK (S : Array (Array Nat)) (s₀ tree : Array Nat)
    (P : Array (Array Nat)) (m : Nat) : Bool :=
  let T := treeConjN 3510 2 #[S[0]!, S[1]!] s₀ tree
  T.size == m &&
    allLt m (fun j => isInvA 3510 T[j]! (invCand 3510 T[j]!) &&
      eqA 3510 (conjA 3510 S[0]! T[j]!) T[(P[0]!)[j]!]! &&
      eqA 3510 (conjA 3510 S[1]! T[j]!) T[(P[1]!)[j]!]!) &&
    allLt m (fun j => allLt j fun k => !(eqA 3510 T[j]! T[k]!))

@[noinline, expose] def fo22OrbitOK (S : Array (Array Nat)) (o : Array Nat)
    (P : Array (Array Nat)) (m : Nat) : Bool :=
  o.size == m && decide (o[m - 1]! < 3510) && allLt (m - 1) (fun j => decide (o[j]! < o[j + 1]!)) &&
    allLt m (fun j => decide ((P[0]!)[j]! < m) && decide ((P[1]!)[j]! < m) &&
      (S[0]!)[o[j]!]! == o[(P[0]!)[j]!]! && (S[1]!)[o[j]!]! == o[(P[1]!)[j]!]!)

@[noinline, expose] def fo22TreeOK (m : Nat) (P : Array (Array Nat)) (ord par gen : Array Nat) :
    Bool :=
  ord.size == m && par.size == m && gen.size == m && isInvA m ord (invCand m ord) &&
    ord[0]! == 0 && allLt m (fun i => i == 0 || (decide (par[i]! < i) && decide (gen[i]! < 2) &&
      (P[gen[i]!]!)[ord[par[i]!]!]! == ord[i]!))

@[noinline, expose] def fo22SubOK (m : Nat) (P : Array (Array Nat))
    (lab ord tpar tgen start : Array Nat) (k : Nat) : Bool :=
  lab.size == m && ord.size == m && tpar.size == m && tgen.size == m && start.size == k + 1 &&
    allLt m (fun p => decide (lab[p]! < k)) && isInvA m ord (invCand m ord) &&
    start[0]! == 0 && start[k]! == m && allLt k (fun c => decide (start[c]! < start[c + 1]!)) &&
    lab[0]! == 0 && ord[0]! == 0 &&
    allLt k (fun c => allLt (start[c + 1]! - start[c]!) fun d =>
      let i := start[c]! + d
      lab[ord[i]!]! == c && (d == 0 ||
        (decide (start[c]! ≤ tpar[i]!) && decide (tpar[i]! < i) &&
          decide (tgen[i]! < P.size) && (P[tgen[i]!]!)[0]! == 0 &&
          (P[tgen[i]!]!)[ord[tpar[i]!]!]! == ord[i]!))) &&
    allLt P.size (fun g => (P[g]!)[0]! != 0 || allLt m fun p => lab[(P[g]!)[p]!]! == lab[p]!)

@[noinline, expose] def fo22OrderOK (m : Nat) (P : Array (Array Nat)) (oa pb e oab : Nat) :
    Bool :=
  eqA m (powA m P[0]! oa) (idA m) && !(eqA m P[0]! (idA m)) &&
    eqA m (powA m P[1]! (pb ^ (e + 1))) (idA m) && !(eqA m (powA m P[1]! (pb ^ e)) (idA m)) &&
    eqA m (powA m (compA m P[0]! P[1]!) oab) (idA m) && !(eqA m (compA m P[0]! P[1]!) (idA m))

@[noinline, expose] def fo22H2OK (Sh hgens : Array (Array Nat)) (s₀ tree : Array Nat)
    (P : Array (Array Nat)) : Bool :=
  let T := treeConjN 3510 3 hgens s₀ tree
  let lvH := rawLevels 3510 Sh fo22HBase
  T.size == 27 &&
    allLt 27 (fun j => isInvA 3510 T[j]! (invCand 3510 T[j]!) &&
      siftA 3510 lvH fo22HBase 0 T[j]! &&
      allLt 3 fun i => decide ((P[i]!)[j]! < 27) &&
        eqA 3510 (conjA 3510 hgens[i]! T[j]!) T[(P[i]!)[j]!]!) &&
    allLt 27 (fun j => allLt 27 fun k => j == k || !(eqA 3510 T[j]! T[k]!)) &&
    allLt 27 (fun j => allLt 27 fun k =>
      eqA 3510 (compA 3510 T[j]! T[k]!) (compA 3510 T[k]! T[j]!))

end CFSG.Sporadic.FischerOddCore
