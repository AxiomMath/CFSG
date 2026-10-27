module

public import Certificates.Data.Kernel.Co2J
public import CFSG.Certificates.Kernel.Bounds.Core3
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_items_root CertificateChecks.KernelSpor.Co2J.SD "Certificates/Kernel/Co2J/data/small.items" 1668 13768123472792105321
#kc_repo #kc_items_root CertificateChecks.KernelSpor.Co2J.JE "Certificates/Kernel/Co2J/data/je.items" 66467 6306576235141878434
#kc_repo #kc_items_root CertificateChecks.KernelSpor.Co2J.JS "Certificates/Kernel/Co2J/data/js.items" 5888 13845202044281108743
#kc_repo #kc_items_root CertificateChecks.KernelSpor.Co2J.PE "Certificates/Kernel/Co2J/data/pe.items" 4352 16355428643030343457
#kc_repo #kc_items_root CertificateChecks.KernelSpor.Co2J.PM "Certificates/Kernel/Co2J/data/pm.items" 1288 5681870476850932627
#kc_repo #kc_items_root CertificateChecks.KernelSpor.Co2J.PS "Certificates/Kernel/Co2J/data/ps.items" 1280 10458659622173174755
#kc_repo #kc_items_root CertificateChecks.KernelSpor.Co2J.PTR "Certificates/Kernel/Co2J/data/pt.items" 3326 2807674318601580329
#kc_repo #kc_items_root CertificateChecks.KernelSpor.Co2J.MRR "Certificates/Kernel/Co2J/data/mr.items" 18459 13336274846372729513
#kc_repo #kc_items_root CertificateChecks.KernelSpor.Co2J.CM "Certificates/Kernel/Co2J/data/cm.items" 2556 2228815177917166393
#kc_repo #kc_items_root CertificateChecks.KernelSpor.Co2J.SM "Certificates/Kernel/Co2J/data/sm.items" 22429 11405247563139469340
#kc_repo #kc_items_root CertificateChecks.KernelSpor.Co2J.EL "Certificates/Kernel/Co2J/data/el.items" 7838 17566282330746174061
#kc_repo #kc_items_root CertificateChecks.KernelSpor.Co2J.EXR "Certificates/Kernel/Co2J/data/ex.items" 64326 7981009918211906659
#kc_repo #kc_items_root CertificateChecks.KernelSpor.Co2J.RC "Certificates/Kernel/Co2J/data/rc.items" 13899 534094591850215273

namespace CertificateChecks.KernelSpor.Co2J

@[expose] noncomputable def G (k : Nat) : Nat := SD k
@[expose] noncomputable def BT : Nat := SD (nat_lit 5)
@[expose] noncomputable def BTi : Nat := SD (nat_lit 6)
@[expose] noncomputable def GJ (i : Nat) : Nat := SD (Nat.add (nat_lit 7) i)
@[expose] noncomputable def JW (i : Nat) : Nat := SD (Nat.add (nat_lit 17) i)
@[expose] noncomputable def JL (i : Nat) : Nat := SD (Nat.add (nat_lit 27) i)
@[expose] noncomputable def MK (k : Nat) : Nat := SD (Nat.add (nat_lit 37) k)
@[expose] noncomputable def INV (q : Nat) : Nat := SD (Nat.add (nat_lit 42) q)

@[expose] noncomputable def PT (s j : Nat) : Nat := fld(PTR s, Nat.mul (nat_lit 16) j, nat_lit 65535)
@[expose] noncomputable def MR (q t : Nat) : Nat := fld(MRR q, Nat.mul (nat_lit 8) t, nat_lit 255)
@[expose] noncomputable def EX (i q : Nat) : Nat := fld(EXR i, Nat.mul (nat_lit 10) q, nat_lit 1023)

end CertificateChecks.KernelSpor.Co2J

end
