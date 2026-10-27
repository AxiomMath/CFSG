module

public import Certificates.Data.Kernel.Misc.O73
public import Certificates.Data.Kernel.Spor.Chain
public import CFSG.LieType.Multipliers.O73DataInputs
public import Mathlib

public section

namespace CFSG.KC.Misc.O73

open CFSG.KC.Enum CFSG.KS CFSG.LieType.Multipliers.O73

@[expose] def idxM (a : Nat) : Idx :=
  if h : a < 3 then .inl ⟨a, h⟩ else if h' : a < 6 then .inr (.inl ⟨a - 3, by omega⟩) else .inr (.inr ())

@[expose] noncomputable def matM7 (A : Matrix Idx Idx (ZMod 3)) : Nat :=
  ofFnM fun a b => (A (idxM a) (idxM b)).val

@[expose] noncomputable def isoM7 (K : Nat) : Bool := Nat.beq (mulM7 (trM7 K) (mulM7 gramM K)) gramM

@[expose] noncomputable def tabM7 (w P K : Nat) : Bool :=
  CFSG.KC.LQT.P.letB K fun K => allN 2187 fun x => Nat.beq (pg w (mask w) P x) (appM7 K x)

@[expose] def expandW (ord : List Nat) (W : List Int) : List Nat :=
  W.flatMap fun l => match l with
    | .ofNat k => [k - 1]
    | .negSucc k => List.replicate (ord.getD k 1 - 1) k

@[expose] noncomputable def wordOK (Ks ord : List Nat) (W : List Int) (j : Nat) : Bool :=
  Nat.beq (Ks.getD j 0) (wordM7 Ks (expandW ord W)) && (expandW ord W).all fun c => Nat.blt c j

end CFSG.KC.Misc.O73

end
