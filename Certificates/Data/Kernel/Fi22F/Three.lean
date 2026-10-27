module

public import CFSG.Sporadic.Presentation.Fi22ExactData
public import CFSG.Certificates.Kernel.Common.Lce
public import CFSG.Certificates.Kernel.Common.Loop
public import CFSG.Certificates.Kernel.Fi22.Bound.Cov
public import CFSG.Certificates.Kernel.Fi22.Bound.Data.Cov
public import Mathlib

public section

namespace CFSG.KC.Fi22F.Three

open CFSG.KC CFSG.KC.Loop CFSG.KC.Fi22B.Cov CFSG.Sporadic.Presentation.Fi22Exact

@[expose] noncomputable def BI : Nat := pw4 CFSG.KD.Fi22BC3.B (nat_lit 12)

@[expose] noncomputable def XF (i : Nat) : Nat :=
  mul4 (mul4 (pw4 BI i) CFSG.KD.Fi22BC3.A) (pw4 CFSG.KD.Fi22BC3.B i)

@[expose] noncomputable def evalL (w : List (Fin 6 × Bool)) : Nat :=
  List.rec (motive := fun _ => Nat) one4 (fun p _ acc => strictN acc (fun x => mul4 (XF p.1.val) x)) w

@[expose] noncomputable def allOne (ws : List (List (Fin 6 × Bool))) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun w _ ih => andB (Nat.beq (evalL w) one4) ih) ws

@[expose] noncomputable def xfOne (i : Nat) : Bool :=
  andB (Nat.blt (XF i) (Nat.shiftLeft (nat_lit 1) (nat_lit 1458))) (Nat.beq (mul4 (XF i) (XF i)) one4)

@[expose] noncomputable def xfOK : Bool :=
  andB (xfOne 0) (andB (xfOne 1) (andB (xfOne 2) (andB (xfOne 3) (andB (xfOne 4) (xfOne 5)))))

@[expose] noncomputable def relsOK : Bool := allOne wsF

@[expose] noncomputable def ord3 (S : Nat) : Bool :=
  andB (Nat.beq (mul4 (mul4 S S) S) one4) (notB (Nat.beq S one4))

@[expose] noncomputable def g1OK : Bool := ord3 (pw4 (evalL Pw) (nat_lit 91))

end CFSG.KC.Fi22F.Three

end
