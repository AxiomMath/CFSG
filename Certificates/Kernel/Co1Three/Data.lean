module

import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.JsonFamilyGz
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_json_family_gz CertificateChecks.KernelCo1Three
  "Certificates/Kernel/Co1Three/data/co1three.json.gz" 5168630 6032295548279544490
  (T : Nat) (W : List Nat)

#kc_repo #kc_json_gz CertificateChecks.KernelCo1Three
  "Certificates/Kernel/Co1Three/data/co1three.json.gz" 5168630 6032295548279544490
  (CH : List (Nat × Nat × List Nat)) (GL : List (List Nat)) (Q : List (List (List Nat)))
  (NZ : List (Nat × List Nat)) (RT : List Nat) (FT : List Nat) (DP : Nat) (XA : Nat)

#kc_select CertificateChecks.KernelCo1Three TS T 28098

#kc_listDispatch CertificateChecks.KernelCo1Three WL W 31
