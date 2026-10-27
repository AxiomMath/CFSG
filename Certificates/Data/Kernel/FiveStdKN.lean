module

public import Certificates.Data.Kernel.FiveStdKPl

public section

namespace CFSG.KC.FiveStdK

@[expose] noncomputable def normAllK (hs gens L : List Nat) : Bool :=
  hs.all fun h => gens.all fun x => L.contains (cjK h (invK h) x)

@[expose] noncomputable def z4K (els : List Nat) : List (Nat × Nat) :=
  els.flatMap fun a => els.filterMap fun b =>
    if Nat.beq (mulK a b) (mulK b a) && decide (ppK a b 4 4).Nodup then some (a, b) else none

@[expose] noncomputable def sylTK (K1 K2 : List Nat) (S : List (Nat × Nat × List Nat))
    (Z4 : List (Nat × Nat)) : Bool :=
  Z4.all fun p => S.all fun q =>
    !(normAllK [p.1, p.2] [q.1, q.2.1] q.2.2) || (normKc K1 K2 p.1 && normKc K1 K2 p.2)

@[expose] noncomputable def nrm2 (a ai b bi x y : Nat) (L : List Nat) : Bool :=
  andB (memL L (cjK a ai x)) <| andB (memL L (cjK a ai y)) <|
    andB (memL L (cjK b bi x)) (memL L (cjK b bi y))

@[expose] noncomputable def sylTE (S : List (Nat × Nat × List Nat)) (E4 : List Nat)
    (Z4 : List (Nat × Nat)) : Bool :=
  Z4.all fun p => orB (andB (memL E4 p.1) (memL E4 p.2)) <|
    letB (invK p.1) fun ai => letB (invK p.2) fun bi =>
      S.all fun q => !(nrm2 p.1 ai p.2 bi q.1 q.2.1 q.2.2)

@[expose] noncomputable def ev5 (n : Nat) : Bool := n % 2 == 0 || n % 5 == 0

@[expose] noncomputable def noInvQ (cs : List Nat) : Bool :=
  cs.any fun x => cs.any fun y => ev5 (ordK (mulK x y))

@[expose] noncomputable def noInvR (H0 : List Nat) (r : Nat) : Bool :=
  noInvQ (H0.map fun h => cjK h (invK h) r)

end CFSG.KC.FiveStdK

end
