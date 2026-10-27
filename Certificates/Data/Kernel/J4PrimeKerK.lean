module

public import Certificates.Data.Kernel.SporSch.J4S11
public import Certificates.Data.Kernel.SporSch.J4SPairK

public section

namespace CFSG.KS.SporSch.J4PK

open CFSG.KC.J4Q CFSG.KS.SporSch.J4E CFSG.KS.SporSch.J4B

@[expose] noncomputable def polyK (c rm one M : Nat) (es : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun e _ ih => Nat.xor (powBJ c rm one (nat_lit 7) M e) ih) es

@[expose] noncomputable def eltK (c rm one A B Bi : Nat) (w : List Int) (e : Nat) : Nat :=
  powBJ c rm one (nat_lit 65) (wFK c rm one A A B Bi w one) e

@[expose] noncomputable def caseK (c rm one A B Bi : Nat) (w : List Int) (e r : Nat)
    (es : List Nat) (P Pi R k : Nat) : Bool :=
  CFSG.KC.J4Q.strictB (eltK c rm one A B Bi w e) fun X =>
    andB (Nat.beq (powBJ c rm one (nat_lit 7) X r) one)
      (fixK c rm one (Nat.xor (polyK c rm one X es) one) P Pi R k)

end CFSG.KS.SporSch.J4PK

end
