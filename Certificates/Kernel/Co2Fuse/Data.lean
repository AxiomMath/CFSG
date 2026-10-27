module

public import Certificates.Data.Kernel.Co2Fuse
public import Certificates.Kernel.Co2Syl.D3
import CFSG.Certificates.Kernel.Bounds.LoadRoot
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_blocked_root CertificateChecks.KernelSpor.Co2Fuse.PT
  "Certificates/Kernel/Co2Fuse/data/pt.bin" 8 4 65535 131072 2134147186599805918

#kc_repo #kc_blocked_root CertificateChecks.KernelSpor.Co2Fuse.CI
  "Certificates/Kernel/Co2Fuse/data/ci.bin" 3 9
  409173825987017733751648712103449894027080255755383098685411421012016724550584319360408761540738019643860835515945008876152157068235674131666065948671
  270272 2305680348648088229

#kc_repo #kc_blocked_root CertificateChecks.KernelSpor.Co2Fuse.CA
  "Certificates/Kernel/Co2Fuse/data/ca.bin" 3 9
  409173825987017733751648712103449894027080255755383098685411421012016724550584319360408761540738019643860835515945008876152157068235674131666065948671
  72576 9298779090560439950

#kc_repo #kc_ktree CertificateChecks.KernelSpor.Co2Fuse CNT
  "Certificates/Kernel/Co2Fuse/data/cnt.bin" 192 4 3072 12098838768288595252

end
