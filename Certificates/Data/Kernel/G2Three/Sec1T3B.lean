module

public import Certificates.Data.Kernel.G2Three.Sec1T3

public section

namespace CFSG.KD.G2Three.Sec1T3

open CFSG.KC.Loop

@[expose] noncomputable def rowLtK (N lo : Nat) : Bool :=
  bAnd(Nat.ble (fld(lo, 8, 255)) (Nat.land lo 255),
    Nat.rec (motive := fun _ => Bool) true
      (fun t ih => bAnd(Nat.blt (Nat.land (pairAt lo t) 511) N, ih)) (Nat.land lo 255))

@[expose] noncomputable def rowsLtK (N : Nat) (LO : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun lo _ ih => bAnd(rowLtK N lo, ih)) LO

end CFSG.KD.G2Three.Sec1T3
