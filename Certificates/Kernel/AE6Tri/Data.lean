module

public import Certificates.Kernel.OmegaEight.AutChainAP
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_json_gz CFSG.KD.AE6Tri "Certificates/Kernel/AE6Tri/data/tri.json.gz" 57117
  9366870501858330739
  (diag : List (List Nat)) (qw : List (List (List Nat))) (delta : List (List (List Nat)))
  (dq : List (List Nat)) (ml : List Nat) (vl : List (List Nat)) (triB : List (List Nat))
  (distV : List (List (List Nat))) (distE : List (List (List Nat)))
  (xc : List Nat) (xci : List Nat) (qg : List (List Nat)) (dg : List (List Nat))
  (orbV0 : List (List Nat)) (orbE0 : List (List Nat)) (orbM : List (List Nat))
  (qnW : List (List (List (List Nat)))) (qdW : List (List (List (List Nat))))
  (qzW : List (List (List Nat))) (qzJ : List (List Nat))

namespace CFSG.KD.AE6Tri

open CertificateChecks.KernelO8

@[expose] noncomputable def RG : List Nat := [AP.S 0, AP.S 1, AP.S 2, AP.S 3, AP.S 4, AP.S 5, AP.S 6,
  AP.S 7]

end CFSG.KD.AE6Tri

end
