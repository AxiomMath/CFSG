
module

public import CFSG.Sporadic.Co2Schreier.ChainCheckBase
public import Std.Data.HashMap
public meta import CFSG.Sporadic.Co2Schreier.ChainCheckBase
public meta import Std.Data.HashMap

public section

namespace CFSG.Sporadic.Co2Schreier

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Monster.B.Mathieu

@[expose] def keyA (t : Array ℕ) : ℕ := t[0]! + 2300 * (t[1]! + 2300 * t[3]!)

structure LeftEnum where
  elems : Array (Array ℕ)
  par : Array ℕ
  lab : Array ℕ
  mult : Array (Array ℕ)
  pos : Std.HashMap ℕ ℕ

@[expose] def leftEnum (gens : Array (Array ℕ)) (cap : ℕ) : LeftEnum := Id.run do
  let mut elems : Array (Array ℕ) := #[idA 2300]
  let mut par : Array ℕ := #[0]
  let mut lab : Array ℕ := #[0]
  let mut mult : Array (Array ℕ) := #[]
  let mut pos : Std.HashMap ℕ ℕ := (∅ : Std.HashMap ℕ ℕ).insert (keyA (idA 2300)) 0
  for h in [0:cap] do
    if h < elems.size then
      let x := elems[h]!
      let mut row : Array ℕ := #[]
      for j in [0:gens.size] do
        let y := compA 2300 gens[j]! x
        match pos.get? (keyA y) with
        | some i => row := row.push i
        | none =>
          pos := pos.insert (keyA y) elems.size
          row := row.push elems.size
          elems := elems.push y
          par := par.push h
          lab := lab.push j
      mult := mult.push row
  return ⟨elems, par, lab, mult, pos⟩

@[expose] def enumOK (gens : Array (Array ℕ)) (m : ℕ) (E : LeftEnum) : Bool :=
  E.elems.size == m && eqA 2300 E.elems[0]! (idA 2300) &&
    allLt m (fun k => isInvA 2300 E.elems[k]! (invCand 2300 E.elems[k]!)) &&
    allLt m (fun k => k == 0 || (decide (E.par[k]! < k) && decide (E.lab[k]! < gens.size) &&
      eqA 2300 E.elems[k]! (compA 2300 gens[E.lab[k]!]! E.elems[E.par[k]!]!))) &&
    allLt m (fun k => allLt gens.size fun j => decide ((E.mult[k]!)[j]! < m) &&
      eqA 2300 E.elems[(E.mult[k]!)[j]!]! (compA 2300 gens[j]! E.elems[k]!)) &&
    allLt m (fun k => E.pos.getD (keyA E.elems[k]!) 0 == k)

@[expose] def conjOK (conj pis : Array (Array ℕ)) (m : ℕ) (E : LeftEnum) : Bool :=
  allLt conj.size fun i => allLt m fun k => decide ((pis[i]!)[k]! < m) &&
    eqA 2300 (compA 2300 (compA 2300 conj[i]! E.elems[k]!) (invCand 2300 conj[i]!))
      E.elems[(pis[i]!)[k]!]!

@[expose] def centerIdx (gens : Array (Array ℕ)) (m : ℕ) (E : LeftEnum) : List ℕ :=
  (List.range m).filter fun k => allLt gens.size fun j => commA E.elems[k]! gens[j]!

@[expose] def enumQ : LeftEnum := leftEnum qArrs 512

@[expose] def enumR : LeftEnum := leftEnum rArrs 2048

@[expose] def centerIdxR : List ℕ :=
  [0, 1, 44, 63, 94, 113, 434, 462, 465, 466, 468, 617, 623, 669, 701, 729, 732, 733, 735, 884,
    890, 936, 1554, 1556, 1557, 1559, 1664, 1730, 1732, 1733, 1735, 1840]

@[noinline, expose] def coreOK (gens conj pis : Array (Array ℕ)) (m : ℕ) (cen : List ℕ)
    (E : LeftEnum) : Bool :=
  enumOK gens m E && conjOK conj pis m E && centerIdx gens m E == cen

end CFSG.Sporadic.Co2Schreier
