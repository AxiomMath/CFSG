module

public import Certificates.Data.Kernel.SporSch.Co1Bfs
public import Certificates.Data.Kernel.Co1B

public section

namespace CFSG.KS.SporSch.M24

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def lane4 (M j : Nat) : Nat :=
  Nat.land (Nat.shiftRight M (Nat.mul (nat_lit 4) j)) (nat_lit 15)

@[expose] noncomputable def sel6 (x₀ x₁ x₂ x₃ x₄ x₅ k : Nat) : Nat :=
  nIf(Nat.beq k (nat_lit 1), x₁, nIf(Nat.beq k (nat_lit 2), x₂, nIf(Nat.beq k (nat_lit 3), x₃,
    nIf(Nat.beq k (nat_lit 4), x₄, nIf(Nat.beq k (nat_lit 5), x₅, x₀)))))

@[expose] noncomputable def ctSixK (GM GIM : Nat → Nat) (ng R M : Nat) : Bool :=
  strictB (ctStepK GM GIM R (lane4 M (nat_lit 1))) fun x₁ =>
  strictB (ctStepK GM GIM R (lane4 M (nat_lit 2))) fun x₂ =>
  strictB (ctStepK GM GIM R (lane4 M (nat_lit 3))) fun x₃ =>
  strictB (ctStepK GM GIM R (lane4 M (nat_lit 4))) fun x₄ =>
  strictB (ctStepK GM GIM R (lane4 M (nat_lit 5))) fun x₅ =>
    ctPinK GM GIM R ng (nat_lit 5) (nat_lit 6) (sel6 R x₁ x₂ x₃ x₄ x₅) (fun _ => nat_lit 0)
      (fun k => lane4 M k) (fun j => lane4 M (Nat.add (nat_lit 6) j))
      (fun k => lane4 M (Nat.add (Nat.add (nat_lit 6) ng) k))

@[expose] noncomputable def fourConjK (GM GIM : Nat → Nat) (ng X M : Nat) : Bool :=
  strictB (CFSG.KC.Co1B.mulWK X X) fun s =>
    bIf(CFSG.KC.Co1B.eqK s idM, true,
      bIf(CFSG.KC.Co1B.eqK (CFSG.KC.Co1B.mulWK s s) idM, ctSixK GM GIM ng X M, true))

end CFSG.KS.SporSch.M24

end
