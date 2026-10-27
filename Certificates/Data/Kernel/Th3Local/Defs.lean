module

public import Certificates.Data.Kernel.ThCent.Pin

public section

namespace CFSG.KC.Th3Local

open CFSG.KC.Th CFSG.KC.Th.BigS

@[expose] noncomputable def ordPk (c rm ONE M p : Nat) : Bool :=
  andB (Nat.beq (powB c rm ONE M p (nat_lit 6)) ONE) (notB (Nat.beq (mulB c rm M ONE) ONE))

@[expose] noncomputable def commPk (c rm M N : Nat) : Bool :=
  Nat.beq (mulB c rm M N) (mulB c rm N M)

end CFSG.KC.Th3Local

end
