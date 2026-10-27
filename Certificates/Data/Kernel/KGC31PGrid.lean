module

public import Certificates.Data.Kernel.KGC31P

public section

namespace CFSG.KC.KGC31P

variable (n w : Nat)

@[expose] noncomputable def pgrid (x y p q : Nat) : List Nat :=
  (List.range p).flatMap fun a => (List.range q).map fun b => pc n w (ppw n w x a) (ppw n w y b)

@[expose] noncomputable def pgridInj (x y p : Nat) : Bool :=
  (List.range p).all fun a => (List.range p).all fun b => (List.range p).all fun c =>
    (List.range p).all fun d => (a == c && b == d) ||
      !(Nat.beq (pc n w (ppw n w x a) (ppw n w y b)) (pc n w (ppw n w x c) (ppw n w y d)))

end CFSG.KC.KGC31P

end
