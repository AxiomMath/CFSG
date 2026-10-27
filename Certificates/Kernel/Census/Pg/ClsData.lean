module

public import CFSG.Certificates.Kernel.Bounds.Core3
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_items_root CertificateChecks.KernelPgCls.W "Certificates/Kernel/Census/Pg/data/words.items" 320 6949180612295703186
#kc_repo #kc_items_root CertificateChecks.KernelPgCls.RW "Certificates/Kernel/Census/Pg/data/repW.items" 82 7195126578818909382
#kc_repo #kc_items_root CertificateChecks.KernelPgCls.TT "Certificates/Kernel/Census/Pg/data/clsT.items" 1395900 10198488982007075698
#kc_repo #kc_items_root CertificateChecks.KernelPgCls.TE "Certificates/Kernel/Census/Pg/data/clsE.items" 82803 10734608103940949857
#kc_repo #kc_items_root CertificateChecks.KernelPgCls.TP "Certificates/Kernel/Census/Pg/data/clsP.items" 69520 14498596744686015576
#kc_repo #kc_items_root CertificateChecks.KernelPgCls.TO "Certificates/Kernel/Census/Pg/data/clsO.items" 61671 4286642774374147757
#kc_repo #kc_items_root CertificateChecks.KernelPgCls.SG "Certificates/Kernel/Census/Pg/data/sylG.items" 37 7149638581764848637
#kc_repo #kc_items_root CertificateChecks.KernelPgCls.SGP "Certificates/Kernel/Census/Pg/data/sylGP.items" 528 12397908485431722462
#kc_repo #kc_items_root CertificateChecks.KernelPgCls.L "Certificates/Kernel/Census/Pg/data/sylL.items" 1081344 10186713258947910701
#kc_repo #kc_items_root CertificateChecks.KernelPgCls.LE "Certificates/Kernel/Census/Pg/data/sylE.items" 98046 12971483842942212447
#kc_repo #kc_items_root CertificateChecks.KernelPgCls.LP "Certificates/Kernel/Census/Pg/data/sylP.items" 55228 17781193730749710497
#kc_repo #kc_items_root CertificateChecks.KernelPgCls.LO "Certificates/Kernel/Census/Pg/data/sylO.items" 48896 3093312747441200625
#kc_repo #kc_items_root CertificateChecks.KernelPgCls.LC "Certificates/Kernel/Census/Pg/data/sylC.items" 41639 1021893083085101787

namespace CertificateChecks.KernelPgCls

@[expose] def offs (j : Nat) : Nat := [0, 36, 63, 1143, 4383, 8703, 9243, 9423, 10143].getD j 0

@[expose] def NC (j : Nat) : Nat := [36, 27, 1080, 3240, 4320, 540, 180, 720, 432].getD j 0

@[expose] noncomputable def Tc (j i : Nat) : Nat := TT (offs j + i)

@[expose] noncomputable def Ec (j i : Nat) : Nat := TE (offs j + i)

@[expose] noncomputable def Pc (j i : Nat) : Nat := TP (offs j + i)

@[expose] noncomputable def Oc (j i : Nat) : Nat := TO (offs j + i)

end CertificateChecks.KernelPgCls
