module

public import Certificates.Data.Kernel.Co2Census
public import Certificates.Kernel.Co2J.Data
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_items_root CertificateChecks.KernelSpor.Co2TInv.TD
  "Certificates/Kernel/Co2Census/data/tinv.items" 33625 13993997751001239619

namespace CertificateChecks.KernelSpor.Co2TInv

@[expose] noncomputable def CL (s : Nat) : Nat := TD s
@[expose] noncomputable def LW (s : Nat) : Nat := TD (Nat.add (nat_lit 15) s)
@[expose] noncomputable def LN (s : Nat) : Nat := TD (Nat.add (nat_lit 30) s)
@[expose] noncomputable def LT (s : Nat) : Nat := TD (Nat.add (nat_lit 45) s)
@[expose] noncomputable def SC (s : Nat) : Nat := TD (Nat.add (nat_lit 60) s)
@[expose] noncomputable def RR (s : Nat) : Nat := TD (Nat.add (nat_lit 75) s)
@[expose] noncomputable def RN (s : Nat) : Nat := TD (Nat.add (nat_lit 90) s)
@[expose] noncomputable def SW (s : Nat) : Nat := TD (Nat.add (nat_lit 105) s)
@[expose] noncomputable def LK (s : Nat) : Nat := TD (Nat.add (nat_lit 120) s)
@[expose] noncomputable def FU (q : Nat) : Nat := TD (Nat.add (nat_lit 135) q)
@[expose] noncomputable def JR (j : Nat) : Nat := TD (Nat.add (nat_lit 206) j)
@[expose] noncomputable def JK (j : Nat) : Nat := TD (Nat.add (nat_lit 237) j)
@[expose] noncomputable def JO (v : Nat) : Nat := TD (Nat.add (nat_lit 268) v)

end CertificateChecks.KernelSpor.Co2TInv

end
