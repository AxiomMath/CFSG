module

public import Certificates.Data.Kernel.SmithD6.StabK
public import Certificates.Data.Kernel.SmithD6.StabTreeK

public section

namespace CFSG.KD.SmithD6Stab

open CFSG.KC.Loop CFSG.KC.KeyTree CFSG.KD.SmithD6ST

@[expose] noncomputable def cntGoN (l : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun a => a)
    (fun k _ ih a => strictN (Nat.add a (Nat.pow 2 (Nat.mul 19 (clsN k)))) ih) l

@[expose] noncomputable def firstGoN (r : Nat → Nat) (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun k _ ih => bAnd(Nat.ble (r (clsN k)) k, ih)) l

@[expose] noncomputable def clsChunkOKN (cs : List (List Nat)) (ns : List Nat) (c : Nat) : Bool :=
  (fun l => bAnd(firstGoN (fun c' => repKeys.getD c' 0) l, Nat.beq (cntGoN l 0) (ns.getD c 0)))
    (nthC cs c)

end CFSG.KD.SmithD6Stab

end
