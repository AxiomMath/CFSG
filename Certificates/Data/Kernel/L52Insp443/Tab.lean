module

public import Certificates.Data.Kernel.L52Insp443.Lin
public import Certificates.Data.CFSGNative.Th.Tables

public section

namespace CFSG.KC.L52I

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc.GLM CFSG.Sporadic.Th.Native

@[expose] noncomputable def tabK (c : Nat) (T : Table) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun i acc => CFSG.KC.Ord.andB (Nat.beq (mvK c (Nat.succ i)) (Nat.succ (ap T i))) acc) (nat_lit 31)

@[expose] noncomputable def unitK (c : Nat) : Bool :=
  CFSG.KC.Ord.andB (Nat.blt c (nat_lit 33554432)) (Nat.beq (rankK c) (nat_lit 5))

@[expose] noncomputable def tabsK : List Nat → List Table → Bool :=
  List.rec (motive := fun _ => List Table → Bool)
    (fun l => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) l)
    (fun c _ ih l => List.rec (motive := fun _ => Bool) false
      (fun T Ts _ => CFSG.KC.Ord.andB (CFSG.KC.Ord.andB (unitK c) (tabK c T)) (ih Ts)) l)

end CFSG.KC.L52I

end
