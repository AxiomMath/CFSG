module

import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.JsonFamilyGz
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_json_family_gz CertificateChecks.KernelCo1Five
  "Certificates/Kernel/Co1Five/data/co1five.json.gz" 3935633 14711953617837968013
  (T : Nat) (W : List Nat) (PA : Nat) (SG : Nat) (CT : Nat)

#kc_repo #kc_json_gz CertificateChecks.KernelCo1Five
  "Certificates/Kernel/Co1Five/data/co1five.json.gz" 3935633 14711953617837968013
  (CH : List (Nat × Nat × List Nat)) (GL : List (List Nat)) (Q : List (List (List Nat)))
  (NQ : Nat) (GQ : List Nat) (GN : List Nat) (RT : List Nat) (FT : List Nat) (DP : Nat)

#kc_select CertificateChecks.KernelCo1Five TS T 21365

#kc_select CertificateChecks.KernelCo1Five PAF PA 625

#kc_select CertificateChecks.KernelCo1Five SGF SG 625

#kc_select CertificateChecks.KernelCo1Five CTF CT 1250

#kc_listDispatch CertificateChecks.KernelCo1Five WL W 23
