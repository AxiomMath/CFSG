module

public import Certificates.Data.Kernel.Misc.PermClos
public import Certificates.Data.Kernel.Co1Seven.Forest
public import Certificates.Kernel.Co1Five.Data

public section

namespace CertificateChecks.KernelCo1Five

open CFSG.KC.Co1Cl CFSG.KC.Co1F2 CFSG.KC.Co1B

@[expose] noncomputable def EQ (k : Nat) : Nat := TS (Nat.add NQ k)

@[expose] noncomputable def qG (j : Nat) : Nat := TS (getL (nat_lit 0) GQ j)

@[expose] noncomputable def ch1023014slp (k : Nat) : Bool := chunkK TS CH WL k

@[expose] noncomputable def ch1023014eq (k : Nat) : Bool := eqsK TS (nat_lit 5) GL (getLLL Q k)

@[expose] noncomputable def ch1023014tree (i : Nat) : Bool :=
  CFSG.KC.Misc.Clos.allR (Nat.mul (nat_lit 125) i) (nat_lit 125)
    (CFSG.KC.Misc.Clos.treeAt mulWK oneK qG (nat_lit 2) EQ PAF)

@[expose] noncomputable def ch1023014sort (i : Nat) : Bool :=
  CFSG.KC.Misc.Clos.allR (Nat.mul (nat_lit 125) i) (nat_lit 125)
    (CFSG.KC.Misc.Clos.sortAt (nat_lit 625) EQ SGF)

@[expose] noncomputable def ch1023014closed (i : Nat) : Bool :=
  CFSG.KC.Misc.Clos.allR (Nat.mul (nat_lit 125) i) (nat_lit 125)
    (CFSG.KC.Misc.Clos.closedAt mulWK qG (nat_lit 2) (nat_lit 625) EQ CTF)

@[expose] noncomputable def ch1023014forest : Bool := cforK TS EQ GN (nat_lit 625) RT DP FT

end CertificateChecks.KernelCo1Five

end
