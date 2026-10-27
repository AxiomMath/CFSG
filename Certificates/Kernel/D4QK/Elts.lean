module

public import Certificates.Data.Kernel.D4QK.Defs
public import Certificates.Kernel.D4QK.Data

public section

namespace CertificateChecks.KernelD4Q

open CFSG.KC.Co1B (mulWK)
open CFSG.KC.D4QK

@[expose] noncomputable def Y1 : Nat := BT.P (nat_lit 1)

@[expose] noncomputable def Y2 : Nat := BT.P (nat_lit 2)

@[expose] noncomputable def ZE : Nat := BT.P (nat_lit 3)

@[expose] noncomputable def R0 : Nat := BT.P (nat_lit 4)

@[expose] noncomputable def S0 : Nat := KT.P (nat_lit 3)

@[expose] noncomputable def Y1I : Nat := powK Y1 (nat_lit 3)

@[expose] noncomputable def S0I : Nat := mulWK S0 S0

@[expose] noncomputable def ZP (i : Nat) : Nat := ZT.P i

@[expose] noncomputable def C1 : Nat := mulWK (mulWK Y1 S0) (mulWK Y1I S0I)

@[expose] noncomputable def C2 : Nat := mulWK (mulWK Y2 S0) (mulWK Y2 S0I)

@[expose] noncomputable def C1I : Nat := mulWK (mulWK S0 Y1) (mulWK S0I Y1I)

@[expose] noncomputable def C2I : Nat := mulWK (mulWK S0 Y2) (mulWK S0I Y2)

end CertificateChecks.KernelD4Q

end
