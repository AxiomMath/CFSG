module

public import Certificates.Data.CFSGNative.SporadicSchreier.MathieuOddCore

public section

namespace CFSG.KC.LocalComp.ThreeW

open CFSG.Sporadic.Schreier.Native CFSG.Sporadic.Th.Native

@[expose] def allFrom (lo : Nat) (p : Nat → Bool) : Nat → Bool
  | 0 => true
  | m + 1 => allFrom lo p m && p (lo + m)

@[expose] def allInK (lo hi : Nat) (p : Nat → Bool) : Bool := allFrom lo p (hi - lo)

@[expose] def tblEqK (n : Nat) (S T : Table) : Bool := allInK 0 n fun i => ap S i == ap T i

@[expose] def commTK (n : Nat) (x y : Table) : Bool := tblEqK n (compT n x y) (compT n y x)

@[expose] def powFixWK (n : Nat) (w : List Table) (e : Nat) : Bool :=
  allInK 0 n fun i => apPowW w e i == i

@[expose] def ordTestK (n m : Nat) (T : Table) : Bool :=
  powFixWK n [T] m && (divParts m).all fun e => !powFixWK n [T] e

@[expose] def closStep (n : Nat) (gens gensInv : Array Table) (h : Nat)
    (st : Array Table × Array Nat × Array Nat × List Nat) :
    Array Table × Array Nat × Array Nat × List Nat :=
  (List.range gens.size).foldl (fun st l =>
    let z := conjT n gens[l]! gensInv[l]! st.1[h]!
    let kz := key n z
    if st.2.2.2.contains kz then st
    else (st.1.push z, st.2.1.push h, st.2.2.1.push l, kz :: st.2.2.2)) st

@[expose] def closLoop (n : Nat) (gens gensInv : Array Table) :
    Nat → Nat → Array Table × Array Nat × Array Nat × List Nat →
      Array Table × Array Nat × Array Nat
  | 0, _, st => (st.1, st.2.1, st.2.2.1)
  | f + 1, h, st =>
    if h < st.1.size then closLoop n gens gensInv f (h + 1) (closStep n gens gensInv h st)
    else (st.1, st.2.1, st.2.2.1)

@[expose] def conjClosureL (n : Nat) (gens gensInv : Array Table) (x : Table) (cap : Nat) :
    Array Table × Array Nat × Array Nat :=
  closLoop n gens gensInv cap 0 (#[x], #[0], #[0], [key n x])

@[expose] def conjTreeOKK (n : Nat) (gens gensInv : Array Table) (x : Table) (elts : Array Table)
    (par lab : Array Nat) : Bool :=
  0 < elts.size && tblEqK n elts[0]! x &&
    allInK 1 elts.size fun k => par[k]! < k && lab[k]! < gens.size &&
      tblEqK n elts[k]! (conjT n gens[lab[k]!]! gensInv[lab[k]!]! elts[par[k]!]!)

@[expose] def witnessCoreK (n : Nat) (gens gensInv : Array Table) (S : Array Table)
    (y : Table) : Bool :=
  S.toList.all (fun s => (List.range gens.size).all fun l =>
      S.toList.any (fun s' => tblEqK n s' (conjT n gens[l]! gensInv[l]! s)) &&
        S.toList.any (fun s' => tblEqK n s' (conjT n gensInv[l]! gens[l]! s))) &&
    S.toList.all (fun s => S.toList.all fun s' => commTK n s s') &&
    S.toList.any (fun s => !commTK n y s) && ordTestK n 3 y

@[expose] def threeWitnessK (n : Nat) (gens gensInv : Array Table) (q y : Table) (cap : Nat) :
    Bool :=
  let c := conjClosureL n gens gensInv q cap
  conjTreeOKK n gens gensInv q c.1 c.2.1 c.2.2 && witnessCoreK n gens gensInv c.1 y

end CFSG.KC.LocalComp.ThreeW

end
