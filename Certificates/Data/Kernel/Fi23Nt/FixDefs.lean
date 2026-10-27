module

public import Certificates.Data.Kernel.Fi23K.Defs

public section

namespace CFSG.KC.Fi23Nt

open CFSG.KC.Enum CFSG.KC.Fi23K

@[expose] noncomputable def memK (F : List Nat) (v : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun p _ ih => bIf(Nat.beq p v, true, ih)) F

@[expose] noncomputable def movK (G : Nat → Nat) (W : List (List Nat)) (v : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false
    (fun w _ ih => bIf(Nat.beq (wv G w v) v, ih, true)) W

@[expose] noncomputable def fixSlK (G : Nat → Nat) (F : List Nat) (W : List (List Nat))
    (lo len : Nat) : Bool :=
  allBlk lo (fun v => bIf(memK F v, true, movK G W v)) len

end CFSG.KC.Fi23Nt

end
