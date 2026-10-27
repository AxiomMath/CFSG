module

public import Certificates.Data.Kernel.Co1End

public section

namespace CFSG.KC.Co1PW

open CFSG.KS.SporSch.M24 CFSG.KC.Co1End

@[expose] noncomputable def okK (N k : Nat) : Bool := Nat.ble 1 k && Nat.ble k N

@[expose] noncomputable def conjPK (M MI : Nat → Nat) (z : Nat) (ps : List Nat) : Nat :=
  ps.foldl (fun acc k => mulK acc (mulK (mulK (M (k - 1)) z) (MI (k - 1)))) idM

@[expose] noncomputable def decK (M MI : Nat → Nat) (N z : Nat) :
    List Nat → List (List Nat) → Bool
  | [], [] => true
  | s :: S, ps :: dec => (ps.all fun k => okK N k && eqK (mulK (M (k - 1)) (MI (k - 1))) idM) &&
      eqK (conjPK M MI z ps) s && decK M MI N z S dec
  | _, _ => false

@[expose] noncomputable def pwCoreK (M MI : Nat → Nat) (N : Nat) (S : List Nat) (iz ih : Nat)
    (dec : List (List Nat)) (R : Nat) : Bool :=
  okK N iz && okK N ih &&
    eqK (mulK (mulK (M (iz - 1)) (M (iz - 1))) (mulK (M (iz - 1)) (M (iz - 1)))) idM &&
    eqK (mulK (M (ih - 1)) (M (iz - 1)))
      (mulK (mulK (mulK (M (iz - 1)) (M (iz - 1))) (M (iz - 1))) (M (ih - 1))) &&
    S.all (fun s => commK s R) && decK M MI N (mulK (M (iz - 1)) (M (iz - 1))) S dec

end CFSG.KC.Co1PW

end
