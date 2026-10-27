module

public import Certificates.Data.Kernel.Co2Cen
public import CFSG.Certificates.Kernel.Bounds.Core3
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_items_root CertificateChecks.KernelSpor.Co2Cen.S21 "Certificates/Kernel/Co2Cen/data/s21.items" 50358 6317755342664306530
#kc_repo #kc_items_root CertificateChecks.KernelSpor.Co2Cen.S71 "Certificates/Kernel/Co2Cen/data/s71.items" 18592 13923204565215770245
#kc_repo #kc_items_root CertificateChecks.KernelSpor.Co2Cen.S28 "Certificates/Kernel/Co2Cen/data/s28.items" 28080 12883537493841357533
#kc_repo #kc_items_root CertificateChecks.KernelSpor.Co2Cen.S78 "Certificates/Kernel/Co2Cen/data/s78.items" 21496 15326247682639634912
#kc_repo #kc_items_root CertificateChecks.KernelSpor.Co2Cen.CS "Certificates/Kernel/Co2Cen/data/cs.items" 1189 11171401221842498570
#kc_repo #kc_items_root CertificateChecks.KernelSpor.Co2Cen.AE "Certificates/Kernel/Co2Cen/data/ae.items" 66480 15913788345978093490
#kc_repo #kc_items_root CertificateChecks.KernelSpor.Co2Cen.AS "Certificates/Kernel/Co2Cen/data/as.items" 5888 3132203721476810812
#kc_repo #kc_items_root CertificateChecks.KernelSpor.Co2Cen.TW "Certificates/Kernel/Co2Cen/data/tw.items" 19952 8522800963181046801

namespace CertificateChecks.KernelSpor.Co2Cen

@[expose] noncomputable def MK1 (k : Nat) : Nat := CS k
@[expose] noncomputable def F1 (i : Nat) : Nat := CS (Nat.add (nat_lit 5) i)
@[expose] noncomputable def JW1 (i : Nat) : Nat := CS (Nat.add (nat_lit 9) i)
@[expose] noncomputable def JL1 (i : Nat) : Nat := CS (Nat.add (nat_lit 19) i)
@[expose] noncomputable def GA (i : Nat) : Nat := CS (Nat.add (nat_lit 29) i)
@[expose] noncomputable def JW8 (i : Nat) : Nat := CS (Nat.add (nat_lit 39) i)
@[expose] noncomputable def JL8 (i : Nat) : Nat := CS (Nat.add (nat_lit 49) i)
@[expose] noncomputable def MK8 (k : Nat) : Nat := CS (Nat.add (nat_lit 59) k)
@[expose] noncomputable def F8 (i : Nat) : Nat := CS (Nat.add (nat_lit 64) i)

end CertificateChecks.KernelSpor.Co2Cen

end
