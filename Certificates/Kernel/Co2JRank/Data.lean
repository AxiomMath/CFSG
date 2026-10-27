module

public import Certificates.Data.Kernel.Co2JRank
public import CFSG.Certificates.Kernel.Bounds.Core3
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_items_root CertificateChecks.KernelSpor.Co2JRank.SC "Certificates/Kernel/Co2JRank/data/sc.items" 1666 8960307786917745748
#kc_repo #kc_items_root CertificateChecks.KernelSpor.Co2JRank.CR "Certificates/Kernel/Co2JRank/data/cr.items" 232931 11803224698922330310
#kc_repo #kc_items_root CertificateChecks.KernelSpor.Co2JRank.CRW "Certificates/Kernel/Co2JRank/data/crw.items" 7107 11835776372810602376

namespace CertificateChecks.KernelSpor.Co2JRank

@[expose] noncomputable def K1 : Nat := SC (nat_lit 0)
@[expose] noncomputable def K3 : Nat := SC (nat_lit 1)
@[expose] noncomputable def CNT : Nat := SC (nat_lit 2)
@[expose] noncomputable def OM : Nat := SC (nat_lit 3)
@[expose] noncomputable def OL : Nat := SC (nat_lit 4)
@[expose] noncomputable def NT : Nat := SC (nat_lit 5)
@[expose] noncomputable def W5 : Nat := SC (nat_lit 6)
@[expose] noncomputable def W3 : Nat := SC (nat_lit 7)
@[expose] noncomputable def C : Nat := SC (nat_lit 8)
@[expose] noncomputable def K1W : Nat := SC (nat_lit 9)
@[expose] noncomputable def WG (k : Nat) : Nat := SC (Nat.add (nat_lit 10) k)

end CertificateChecks.KernelSpor.Co2JRank

end
