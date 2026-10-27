module

public import Certificates.Data.Kernel.LocalQT.Syl24

public section

namespace CFSG.KC.LQT.Syl

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.LQT.S CFSG.KC.LQT.W CFSG.KC.LQT.T2

@[expose] noncomputable def rlGK (n : Nat) (G : List Nat) (rgw rwords : List (List Int)) :
    List Nat :=
  List.map (evalZK n (List.map (evalZK n G) rgw)) rwords

@[expose] noncomputable def subOK (n a : Nat) (L E : List Nat) : Bool :=
  allBs [Nat.ble n 32, Nat.beq (lenL E) (Nat.pow 2 a), distinctS E, memL (one n) E,
    allL E (fun x => allL E fun y => memL (mul n x y) E), allL E fun x => memL x L]

@[expose] noncomputable def heavyK (n : Nat) (L E : List Nat) (m : Nat) : List Nat :=
  filtL (invK n L) fun x => andB (notB (memL x E))
    (Nat.ble m (lenL (filtL (invK n L) fun y => andB (notB (Nat.beq y x)) (comm n x y))))

end CFSG.KC.LQT.Syl

end
