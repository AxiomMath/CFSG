module

public import Certificates.Data.Kernel.Co2Cls
public import Certificates.Kernel.Co2Syl.Small
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_json_gz CertificateChecks.KernelSpor.Co2Cls
  "Certificates/Kernel/Co2Cls/data/small.json.gz" 36619 15703106123726903873
  (HL : List Nat)
  (O1 : List Nat) (IX1 : List Nat) (K1 : Nat) (W1 : List Nat)
  (O2 : List Nat) (IX2 : List Nat) (K2 : Nat) (W2 : List Nat)
  (O3 : List Nat) (IX3 : List Nat) (K3 : Nat) (W3 : List Nat)
  (O4 : List Nat) (IX4 : List Nat) (K4 : Nat)
  (O5 : List Nat) (IX5 : List Nat) (K5 : Nat) (W5 : List Nat)
  (O6 : List Nat) (IX6 : List Nat) (K6 : Nat) (W6 : List Nat)
  (O7 : List Nat) (IX7 : List Nat) (K7 : Nat) (W7 : List Nat)
  (O8 : List Nat) (IX8 : List Nat) (K8 : Nat) (W8 : List Nat)
  (O9 : List Nat) (IX9 : List Nat) (K9 : Nat) (W9 : List Nat)

namespace CertificateChecks.KernelSpor.Co2Cls

open CertificateChecks.KernelSpor.Co2Syl

@[expose] noncomputable def GC (j : Nat) : Nat := lAt LT (Nat.add j (nat_lit 21))

@[expose] noncomputable def HT (l : Nat) : Nat := lAt HL l

end CertificateChecks.KernelSpor.Co2Cls

end
