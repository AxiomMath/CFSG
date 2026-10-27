module

public import Certificates.Data.Kernel.LocalQT.Perm

public section

namespace CFSG.KC.Misc.C23340

open CFSG.KC.Ord CFSG.KC.LQT.P

@[expose] noncomputable def p45 (v : Nat) : Bool := Nat.beq (pow 6 v 45) (one 6)

@[expose] noncomputable def wit (s u : Nat) : Bool :=
  impB (p45 u) (anyC 6 s fun c =>
    andB (even 6 c) (notB (p45 (mul 6 (mul 6 (mul 6 (inv 6 u) c) u) (inv 6 c)))))

@[expose] noncomputable def chk23340 : Bool :=
  allP 6 fun s => impB (Nat.beq (mul 6 s s) (one 6)) (allC 6 s fun u =>
    impB (even 6 u) (impB (notB (Nat.beq u (one 6))) (wit s u)))

end CFSG.KC.Misc.C23340

end
