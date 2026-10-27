module

public import Certificates.Data.CFSGNative.J4Tree.Aff
public import Certificates.Data.Kernel.F2Word

public section

namespace CFSG.KC.J4Tree

open CFSG.J4Tree.Native CFSG.KC.F2W

@[expose] def packL (l : List Nat) : Nat := l.foldr (fun x acc => x + 4096 * acc) 0

@[expose] def pkC (a : Code) : Nat := packL a.rows.toList

@[expose] def oneK : Nat := pkC 1

@[expose] def tblC (L : Array Code) : List Nat := L.toList.map pkC

@[expose] def letK (X Xi : List Nat) (ℓ : Int) : Nat :=
  if 0 < ℓ then X.getD (ℓ.toNat - 1) oneK else Xi.getD ((-ℓ).toNat - 1) oneK

@[expose] noncomputable def wordCK (X Xi : List Nat) (w : List Int) : Nat :=
  w.foldl (fun acc ℓ => mulW 12 acc (letK X Xi ℓ)) oneK

@[expose] noncomputable def etaCK (U : List Nat) (c : Nat) : Nat :=
  (List.range 11).foldl (fun acc j => if c.testBit j then mulW 12 acc (U.getD j oneK) else acc) oneK

@[expose] def projN (x : Nat) : Nat :=
  (List.range 112).foldl (fun acc j => if x.testBit j then acc ^^^ (projP[j]?.getD 0) else acc) 0

end CFSG.KC.J4Tree

end
