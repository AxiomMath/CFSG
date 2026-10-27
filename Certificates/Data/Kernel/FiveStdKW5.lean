module

public import Certificates.Data.Kernel.FiveStdKW4

public section

namespace CFSG.KC.FiveStdK

@[expose] noncomputable def wlK (K1 : List Nat) (u : Nat) : List Nat :=
  K1.filter fun w => Nat.beq (mulK w w) zK && Nat.beq (cjK w (invK w) u) (mulK u zK)

@[expose] noncomputable def sylInvK (S : List (Nat × Nat × List Nat)) (a b : Nat) :
    List (Nat × Nat × List Nat) :=
  S.filter fun q => normAllK [a, b] [q.1, q.2.1] q.2.2

@[expose] noncomputable def x1K (K1 : List Nat) (t g : Nat) (S : List (Nat × Nat × List Nat)) (w : Nat) :
    Bool :=
  letB (cjK t (invK t) w) fun w2 =>
    Nat.beq (mulK w w2) (mulK w2 w) && eqLK (closureK [g, w]) K1 &&
      S.all fun q => (ppK w w2 4 4).any fun v =>
        eqLK q.2.2 ((ppK g (cjK t (invK t) g) 5 5).map (cjK v (invK v)))

@[expose] noncomputable def checkWK (K1 : List Nat) (t u g : Nat) (S : List (Nat × Nat × List Nat)) : Bool :=
  (wlK K1 u).all (x1K K1 t g S)

end CFSG.KC.FiveStdK

end
