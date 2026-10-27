module

public import Certificates.Data.Kernel.Ivk8Norm
public import CFSG.Certificates.Kernel.Common.Loop

public section

namespace CFSG.KS.Ivk8KBStarV

open CFSG.Certificates.Kernel.PkEnum CFSG.KS.Ivk8Norm

@[expose] noncomputable def powV {n : Nat} (a : VP n) (k : Nat) : VP n :=
  Nat.rec (motive := fun _ => VP n) (oneV n) (fun _ ih => mulV ih a) k

@[expose] noncomputable def witAny {n : Nat} (p : Nat) (W : List (VP n)) (z : VP n) : Bool :=
  List.rec (motive := fun _ => Bool) false
    (fun c _ ih => bIf(difV (powV (mulV z (conjV c z)) p) (oneV n), true, ih)) W

@[expose] noncomputable def rowZ {n : Nat} (p : Nat) (W : List (VP n)) (z : VP n) : Bool :=
  bIf(difV (powV z p) (oneV n), true, bIf(difV z (oneV n), witAny p W z, true))

@[expose] noncomputable def rowOK {n : Nat} (p : Nat) (W K : List (VP n)) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun z _ ih => bAnd(rowZ p W z, ih)) K

@[expose] noncomputable def movesZ {n : Nat} (d z : VP n) : Bool :=
  bIf(difV z (oneV n), movesV d z, true)

@[expose] noncomputable def movesOK {n : Nat} (d : VP n) (K : List (VP n)) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun z _ ih => bAnd(movesZ d z, ih)) K

end CFSG.KS.Ivk8KBStarV

end
