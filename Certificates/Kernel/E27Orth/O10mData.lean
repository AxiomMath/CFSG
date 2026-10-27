module

public import CFSG.Certificates.Kernel.Bounds.Core3
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_items_root CertificateChecks.KernelE27Orth.O10m.D "Certificates/Kernel/E27Orth/data/o10m.items" 107213 3338193239670807758

namespace CertificateChecks.KernelE27Orth.O10m

@[expose] noncomputable def G (j : Nat) : Nat := D j
@[expose] noncomputable def Y (j : Nat) : Nat := D (Nat.add (nat_lit 5) j)
@[expose] noncomputable def Yi (j : Nat) : Nat := D (Nat.add (nat_lit 10) j)
@[expose] noncomputable def U : Nat := D (nat_lit 15)
@[expose] noncomputable def E (i : Nat) : Nat := D (Nat.add (nat_lit 16) i)
@[expose] noncomputable def Tr (i : Nat) : Nat := D (Nat.add (nat_lit 745) i)
@[expose] noncomputable def Ss (k : Nat) : Nat := D (Nat.add (nat_lit 1474) k)
@[expose] noncomputable def Lf (q : Nat) : Nat := D (Nat.add (nat_lit 2203) q)
@[expose] noncomputable def W (i : Nat) : Nat := D (Nat.add (nat_lit 5848) i)
@[expose] noncomputable def Rp (r : Nat) : Nat := D (Nat.add (nat_lit 6577) r)
@[expose] noncomputable def Cm (q : Nat) : Nat := D (Nat.add (nat_lit 6730) q)

end CertificateChecks.KernelE27Orth.O10m

end
