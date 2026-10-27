module

public import Certificates.Data.Kernel.SporSch.HS2272K

public section

namespace CFSG.KS.HS7208

open CFSG.KC.Enum

@[expose] noncomputable def memN (i : Nat) (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun a _ ih => bIf(Nat.beq a i, true, ih)) l

@[expose] noncomputable def ncW (n : Nat) (f g : Nat → Nat) (p : Nat) : Bool :=
  bAnd(Nat.blt p n, bIf(Nat.beq (f (g p)) (g (f p)), false, true))

@[expose] noncomputable def ordK (n : Nat) (K : Nat → Nat) (i : Nat) : Bool :=
  bIf(Nat.blt (Nat.succ i) n, Nat.blt (K i) (K (Nat.succ i)), true)

end CFSG.KS.HS7208

end
