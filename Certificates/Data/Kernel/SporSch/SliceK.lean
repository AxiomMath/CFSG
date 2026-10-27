module

public import Certificates.Data.Kernel.SporSch.MathieuOC

public section

namespace CFSG.KS.SporSch.MOC

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

@[expose] noncomputable def anyLtK (f : Nat → Bool) : Nat → Bool :=
  Nat.rec (motive := fun _ => Bool) false
    (fun j ih => Bool.rec (motive := fun _ => Bool) ih true (f j))

@[expose] noncomputable def trOrbK (n w : Nat) (LR TR : Nat → Nat) (b₀ b₁ : Nat) : Bool :=
  allN (Nat.sub (rcnt (LR (nat_lit 0))) (nat_lit 1)) fun i =>
    anyLtK (fun j => Nat.beq
        (pg w (mask w) (TR (Nat.add (roff n (Nat.mul n w) (LR (nat_lit 1))) j)) b₁)
        (pg w (mask w) (TR (Nat.add (roff n (Nat.mul n w) (LR (nat_lit 0))) (Nat.succ i))) b₀))
      (rcnt (LR (nat_lit 1)))

end CFSG.KS.SporSch.MOC
