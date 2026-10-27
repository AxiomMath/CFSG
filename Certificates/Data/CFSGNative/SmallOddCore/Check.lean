module

public import Certificates.Data.CFSGNative.SporadicSchreier.Classes
public import Certificates.Data.CFSGNative.Schreier.Check

public section

namespace CFSG.Sporadic.SmallOddCore.Native

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native

@[expose] def hkey (n : Nat) (T : Table) : UInt64 :=
  Nat.fold n (fun i _ h => (h ^^^ (T[i]!).toUInt64) * 1099511628211) 14695981039346656037

@[expose] def hkeysDistinct (n : Nat) (Ts : List Table) : Bool :=
  strictlyIncreasing ((Ts.map fun T => (hkey n T).toNat).mergeSort)

@[expose] def conjClosureH (n : Nat) (gens gensInv : Array Table) (x : Table) (cap : Nat) :
    Array Table × Array Nat × Array Nat := Id.run do
  let mut seen : Std.HashSet UInt64 := (∅ : Std.HashSet UInt64).insert (hkey n x)
  let mut elts : Array Table := #[x]
  let mut par : Array Nat := #[0]
  let mut lab : Array Nat := #[0]
  for h in [0:cap] do
    if h < elts.size then
      let y := elts[h]!
      for l in [0:gens.size] do
        let z := conjT n gens[l]! gensInv[l]! y
        let kz := hkey n z
        if !seen.contains kz then
          seen := seen.insert kz
          elts := elts.push z
          par := par.push h
          lab := lab.push l
    else break
  return (elts, par, lab)

@[expose] def mulClosureH (n : Nat) (gens : Array Table) (cap : Nat) :
    Array Table × Array Nat × Array Nat := Id.run do
  let e := idT n
  let mut seen : Std.HashSet UInt64 := (∅ : Std.HashSet UInt64).insert (hkey n e)
  let mut elts : Array Table := #[e]
  let mut par : Array Nat := #[0]
  let mut lab : Array Nat := #[0]
  for h in [0:cap] do
    if h < elts.size then
      let y := elts[h]!
      for l in [0:gens.size] do
        let z := compT n y gens[l]!
        let kz := hkey n z
        if !seen.contains kz then
          seen := seen.insert kz
          elts := elts.push z
          par := par.push h
          lab := lab.push l
    else break
  return (elts, par, lab)

@[expose] def mulTreeOK (n : Nat) (gens : Array Table) (elts : Array Table) (par lab : Array Nat) :
    Bool :=
  0 < elts.size && tblEq n elts[0]! (idT n) &&
    allIn 1 elts.size fun k => par[k]! < k && lab[k]! < gens.size &&
      tblEq n elts[k]! (compT n elts[par[k]!]! gens[lab[k]!]!)

@[expose] def memT (n : Nat) (L : Array Table) (x : Table) : Bool := L.any (tblEq n x)

@[expose] def closedOK (n : Nat) (gens : Array Table) (L : Array Table) : Bool :=
  L.all fun x => gens.all fun g => memT n L (compT n x g)

@[inline, expose] def hexDigit (c : UInt8) : Nat :=
  if c.toNat < 58 then c.toNat - 48 else c.toNat - 55

@[expose] def hexNum (b : ByteArray) (o : Nat) : Nat → Nat
  | 0 => 0
  | w + 1 => hexNum b o w * 16 + hexDigit (b.get! (o + w))

@[expose] def hexT (w n k₀ : Nat) (s : String) : Table :=
  let b := s.toUTF8
  Array.ofFn (n := n) fun i => UInt32.ofNat (hexNum b (w * (k₀ + i.val)) w)

@[expose] def natArr (T : Table) : Array Nat := T.map (·.toNat)

end CFSG.Sporadic.SmallOddCore.Native
