module

public import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import Std.Data.HashMap

public section

namespace CFSG.YGroups.DCE

open CFSG.Monster.B.Co2.Native

@[expose] def hmod (_ : Unit := ()) : Nat := 36028797018963968

@[expose] def weights (n : Nat) : Array Nat := Id.run do
  let mut s : UInt64 := 0x2545F4914F6CDD1D
  let mut out : Array Nat := Array.mkEmpty n
  for _ in [0:n] do
    s := s + 0x9E3779B97F4A7C15
    let z := (s ^^^ (s >>> 30)) * 0xBF58476D1CE4E5B9
    let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
    let z := z ^^^ (z >>> 31)
    out := out.push (z.toNat % hmod)
  return out

structure XData where
  n : Nat
  m : Nat
  N : Nat
  XT : Array Nat
  par : Array Nat
  lab : Array Nat
  dist : Array Nat
  R : Array Nat
  find : Std.HashMap Nat Nat

@[inline, expose] def sumMod (m : Nat) (f : Nat → Nat) : Nat :=
  Nat.fold m (fun k _ h => h + f k) 0

@[expose] def rowHash (D : XData) (i : Nat) : Nat :=
  sumMod D.m fun k => D.R[D.XT[D.m * i + k]!]!

@[expose] def imgHash (D : XData) (σ : Array Nat) (i : Nat) : Nat :=
  sumMod D.m fun k => D.R[σ[D.XT[D.m * i + k]!]!]!

@[expose] def act (D : XData) (σ : Array Nat) (i : Nat) : Nat :=
  D.find.getD (imgHash D σ i) D.N

@[expose] def mkXData (n : Nat) (gens : Array (Array Nat)) (X0 : Array Nat) (cap : Nat) :
    XData := Id.run do
  let m := X0.size
  let R := weights n
  let mut XT : Array Nat := X0
  let mut par : Array Nat := #[0]
  let mut lab : Array Nat := #[0]
  let mut dist : Array Nat := #[0]
  let mut find : Std.HashMap Nat Nat := {}
  find := find.insert (sumMod m fun k => R[X0[k]!]!) 0
  let mut head := 0
  let mut cnt := 1
  for _ in [0:cap] do
    if head < cnt then
      for l in [0:gens.size] do
        let σ := gens[l]!
        let h := sumMod m fun k => R[σ[XT[m * head + k]!]!]!
        if !(find.contains h) then
          find := find.insert h cnt
          for k in [0:m] do
            XT := XT.push σ[XT[m * head + k]!]!
          par := par.push head
          lab := lab.push l
          dist := dist.push (dist[head]! + 1)
          cnt := cnt + 1
      head := head + 1
    else
      break
  return { n, m, N := cnt, XT, par, lab, dist, R, find }

@[expose] def rowNodup (n : Nat) (X0 : Array Nat) : Bool :=
  allLt X0.size (fun a => decide (X0[a]! < n) &&
    allLt X0.size fun b => a == b || X0[a]! != X0[b]!)

@[expose] def mapsInto (X0 : Array Nat) (σ : Array Nat) : Bool :=
  allLt X0.size fun a => X0.contains σ[X0[a]!]!

@[expose] def xtOK (D : XData) (gens : Array (Array Nat)) (X0 : Array Nat) (fix : List Nat) :
    Bool :=
  D.m == X0.size && D.n ≠ 0 && 0 < D.N && D.XT.size == D.N * D.m && D.R.size == D.n &&
    D.par.size == D.N && D.lab.size == D.N && D.dist.size == D.N &&
    rowNodup D.n X0 && allLt D.m (fun k => D.XT[k]! == X0[k]!) &&
    fix.all (fun l => decide (l < gens.size) && mapsInto X0 gens[l]!) &&
    allLt D.N (fun i => i == 0 || (decide (D.par[i]! < D.N) && decide (D.lab[i]! < gens.size) &&
      decide (D.dist[D.par[i]!]! < D.dist[i]!) &&
      allLt D.m fun k => D.XT[D.m * i + k]! == gens[D.lab[i]!]![D.XT[D.m * D.par[i]! + k]!]!)) &&
    allLt D.N fun i => D.find.get? (rowHash D i) == some i

end CFSG.YGroups.DCE
