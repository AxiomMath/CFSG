module

public import Certificates.Data.Kernel.Co1M.InvFam

public section

namespace CFSG.KC.U6Odd

open CFSG.KLie.CT CFSG.KC.InvFam

@[expose] noncomputable def coordK (P : List Nat) (w : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun p _ ih i => Nat.lor (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (pw2 i) (bit w p))
      (ih (Nat.succ i))) P (nat_lit 0)

@[expose] noncomputable def labC (P : List Nat) (T w : Nat) : Nat := fget T (coordK P w) (nat_lit 2)

@[expose] noncomputable def labCK (L : Nat → Nat) (P : List Nat) (T : Nat) (W : List Nat) : Bool :=
  allL W fun w => Nat.beq (labC P T w) (L w)

end CFSG.KC.U6Odd

end
