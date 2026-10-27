module

import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.JsonFamilyGz
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_json_family_gz CertificateChecks.KernelCo1Seven
  "Certificates/Kernel/Co1Seven/data/co1seven.json.gz" 769511 14015671660612536961
  (T : Nat) (W : List Nat)

#kc_repo #kc_json_gz CertificateChecks.KernelCo1Seven
  "Certificates/Kernel/Co1Seven/data/co1seven.json.gz" 769511 14015671660612536961
  (CH : List (Nat × Nat × List Nat)) (GL : List (List Nat)) (Q : List (List (List Nat))) (SN : Nat)

#kc_select CertificateChecks.KernelCo1Seven TS T 4189

#kc_listDispatch CertificateChecks.KernelCo1Seven WL W 7
