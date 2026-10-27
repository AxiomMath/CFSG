module

public import Certificates.Data.Kernel.Hall82K.Affine
public import CFSG.CGT.Hall82.DModelData

public section

namespace CFSG.KC.Hall82K

open CFSG.CGT.Hall82

@[expose] noncomputable def codeArrK (c : Nat) (a : Array Nat) : Bool :=
  band (Nat.beq a.size 64) (allN (fun v => Nat.beq (a.getD v 0) (apL c v)) 64)

@[expose] noncomputable def zipArrK (L : List Nat) (A : List (Array Nat)) : Bool :=
  List.rec (motive := fun _ => List (Array Nat) → Bool)
    (fun B => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) B)
    (fun c _ ih B => List.rec (motive := fun _ => Bool) false
      (fun a B' _ => band (codeArrK c a) (ih B')) B) L A

@[expose] noncomputable def q0BridgeK : Bool :=
  allN (fun k => beqB (hallQ0List.getD k false) (Nat.beq (bitN q0K k) 1)) 64

@[expose] noncomputable def wBridgeK : Bool :=
  allN (fun k => beqB (memL k hallWList) (Nat.beq (bitN wK k) 1)) 64

@[expose] noncomputable def qtBridgeK : Bool :=
  allN (fun a => allN (fun x =>
    Nat.beq (bitN (Nat.land (Nat.shiftRight qtK (Nat.shiftLeft a 6)) fullK) x)
      (bitN q0K (Nat.xor x a))) 64) 64

@[expose] noncomputable def idxBridgeK : Bool :=
  allN (fun x => Nat.beq (idxB (Nat.shiftLeft 1 x)) x) 64

end CFSG.KC.Hall82K
