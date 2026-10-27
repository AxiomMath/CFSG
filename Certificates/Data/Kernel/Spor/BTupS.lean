module

public import Certificates.Data.Kernel.Spor.BTupO

public section

namespace CFSG.KS.BTup

open CFSG.KC.Enum CFSG.KS.Row

@[expose] noncomputable def btSh (w d : Nat) (f : Nat → Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun t ih => Nat.add ih (Nat.shiftLeft (f t) (Nat.mul w t))) d

@[expose] noncomputable def btCjKy (w m d : Nat) (G R PRE : Nat → Nat) (c j s : Nat) : Nat :=
  btSh w d (fun t => pg w m c (btWalk w m G R s (btPre PRE d j t)))

@[expose] noncomputable def btCjSum (w m d cnt : Nat) (G R PRE : Nat → Nat) (c j : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun s ih => strictN ih (fun a => Nat.add a (btCjKy w m d G R PRE c j s))) cnt

@[expose] noncomputable def btSv (SV : Nat → Nat) (j : Nat) : Nat :=
  rg (nat_lit 64) (nat_lit 18446744073709551615) SV (nat_lit 0) j

@[expose] noncomputable def btCjSK (n w m d cnt B : Nat) (G R PRE SV : Nat → Nat) (c j : Nat) :
    Bool :=
  bAnd(allN d (fun t => bAnd(Nat.blt (btPre PRE d j t) n,
    Nat.beq (pg w m c (btPre PRE d j t)) (pg w m B t))),
    Nat.beq (btCjSum w m d cnt G R PRE c j) (btSv SV j))

@[expose] noncomputable def btIncK (cnt : Nat) (SV : Nat → Nat) : Bool :=
  allN cnt (fun j => bIf(Nat.blt (Nat.succ j) cnt, Nat.blt (btSv SV j) (btSv SV (Nat.succ j)), true))

@[expose] noncomputable def btSgK (w m d kw km cnt ws ms : Nat) (G K R PRE : Nat → Nat) (S c j : Nat) :
    Bool :=
  allN cnt (fun s => strictB (pg ws ms S s) (fun u => bAnd(Nat.blt u cnt,
    allN d (fun t => Nat.beq (pg w m (btKey kw km K u) t)
      (pg w m c (btWalk w m G R s (btPre PRE d j t)))))))

end CFSG.KS.BTup

end
