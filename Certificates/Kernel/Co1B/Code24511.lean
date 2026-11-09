module

public meta import Certificates.Kernel.SporSch.HN.GenNTree
public import Certificates.Kernel.SporSch.HN.GenNTree
import CFSG.Assembly.Defs

public section

private meta def CertificateChecks.KernelCo1B.H24511.codes24511 : List Nat :=
  (String.splitOn (include_str "Code24511.0.txt") ",").map String.toNat!

#kss_ntree CertificateChecks.KernelCo1B.H24511.CC CertificateChecks.KernelCo1B.H24511.codes24511

end
