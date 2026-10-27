module

public import Certificates.Data.Kernel.L34Cov.AlphaGen

public section

namespace CFSG.KC.L34Cov

open CFSG.KC CFSG.KC.Loop CFSG.Certificates.CosetEnumeration

@[expose] def liftCodes (L : List (List (Fin 2 × Bool) × List (Fin 2 × Bool) × Nat)) :
    List (List Nat × List Nat × Nat) :=
  L.map fun x => (x.1.map letterCode, x.2.1.map letterCode, x.2.2)

@[expose] noncomputable def liftIdOK (V : Nat) (TA TB : Nat → Nat) (U : List (List Nat))
    (vA vB : Nat) (x : List Nat × List Nat × Nat) : Bool :=
  zvOK V TA TB (x.1 ++ substC U x.2.1) (corrC x.2.2 vA vB (eN 0 x.2.1) (eN 1 x.2.1))

@[expose] noncomputable def liftsOK (V : Nat) (TA TB : Nat → Nat) (F : List (List Nat))
    (uA uB : List Nat) (L : List (List Nat × List Nat × Nat)) : Bool :=
  bindB (zvC V TA TB (invW uA ++ substC [uA, uB] (F.getD 0 []))) fun vA =>
  bindB (zvC V TA TB (invW uB ++ substC [uA, uB] (F.getD 1 []))) fun vB =>
    andB (zvOK V TA TB (invW uA ++ substC [uA, uB] (F.getD 0 [])) vA)
    (andB (zvOK V TA TB (invW uB ++ substC [uA, uB] (F.getD 1 [])) vB)
      (L.all (liftIdOK V TA TB [uA, uB] vA vB)))

end CFSG.KC.L34Cov

end
