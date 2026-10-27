module

public import Certificates.Data.CFSGNative.HS.SmallF2

public section

namespace CFSG.Sporadic.Co1Schreier.Native

open CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Th.Native

@[expose] def parentsOf (O : VOrbit) (n : Nat) : Array Nat := Id.run do
  let mut par : Array Nat := Array.replicate n 0
  let mut next : Nat := 1
  for h in [0:n] do
    if ap O.alpha h == next then
      par := par.set! next h
      next := next + 1
    if ap O.beta h == next then
      par := par.set! next h
      next := next + 1
  return par

@[expose] def connOK (O : VOrbit) (par : Array Nat) (n : Nat) : Bool :=
  allIn 1 n fun j => decide (par[j]! < j) && (ap O.alpha par[j]! == j || ap O.beta par[j]! == j)

@[expose] def enumOK (cP cQ : Array Nat) (root n : Nat) (O : VOrbit) : Bool :=
  vOrbitOK 24 n cP cQ O && O.pts[0]! == root && connOK O (parentsOf O n) n

end CFSG.Sporadic.Co1Schreier.Native
