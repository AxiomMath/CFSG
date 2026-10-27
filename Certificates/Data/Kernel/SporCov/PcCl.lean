module

public import Certificates.Data.Kernel.SporCov.PCl

public section

namespace CFSG.KC.SporCov

@[expose] noncomputable def pcAll (E : List Nat → List Nat → Bool) (p : Nat) (H Rl : List (List Nat))
    (k : Nat) : Bool :=
  allLt k fun i => allLt k fun j => cond (Nat.ble i j) (pcR E p H Rl k i j) true

@[expose] noncomputable def pccOK (E : List Nat → List Nat → Bool) (L : Nat → Bool) (p k nL nE nR : Nat)
    (H Rl : List (List Nat)) (t : List Nat) (M Y Hc Yc C R : List (List Nat)) (K : List Nat) : Bool :=
  chA L H && pcAll E p H Rl k && pclOK E L nL nE nR (nthW H 0) (nthW H 1) t M Y Hc Yc C R K &&
    E (repW t p) [] && neOK E t

end CFSG.KC.SporCov

end
