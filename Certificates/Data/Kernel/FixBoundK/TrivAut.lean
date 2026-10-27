module

public import Certificates.Data.Kernel.FixBoundK.Triv

public section

namespace CFSG.KC.FixBoundK.Triv

open CFSG.KLie.CT CFSG.KC.FixBoundK CFSG.KC.Loop

@[expose] noncomputable def codeL (bs : List Nat) : Bool :=
  bAnd(Nat.beq (sumBelow (nat_lit 4096) (nat_lit 64)
      (fun m => nIf(Nat.beq (actK bs m) (nat_lit 0), nat_lit 1, nat_lit 0))) (nat_lit 1),
    allS (fun b => bAnd(Nat.beq (synK b) (nat_lit 0), Nat.blt b (pw2 (nat_lit 24)))) bs)

@[expose] noncomputable def codeK : Bool := codeL bmL

@[expose] noncomputable def permG (G : Nat) : Bool :=
  allN (nat_lit 24) fun j => andB (Nat.blt (fget G j (nat_lit 5)) (nat_lit 24))
    (allN j fun i => notB (Nat.beq (fget G i (nat_lit 5)) (fget G j (nat_lit 5))))

@[expose] noncomputable def autG (G : Nat) : Bool :=
  andB (permG G) (allS (fun b => Nat.beq (synK (pmK G b)) (nat_lit 0)) bmL)

@[expose] noncomputable def autK (GS GA : Nat) : Bool := allN (nat_lit 12) fun k => autG (genK GS GA k)

end CFSG.KC.FixBoundK.Triv

end
