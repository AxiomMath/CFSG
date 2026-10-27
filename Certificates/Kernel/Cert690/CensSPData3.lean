module

public import Init
public meta import CFSG.Certificates.Kernel.Common.JsonGz
public meta import CFSG.Certificates.Kernel.Common.Repo
public import CFSG.Certificates.Kernel.Common.JsonGz
public import CFSG.Certificates.Kernel.Common.Repo

set_option maxRecDepth 400000

public section

#kc_repo #kc_json_gz CertificateChecks.KernelC690.CensSP3
  "Certificates/Kernel/Cert690/data/CensSP3.json.gz" 1974634 17400648496689204911
  (lo : Nat) (ginv : List (List Nat)) (wg : List (List (List Nat)))
  (cpar : List (List (Nat × Nat))) (T : List (List (Nat × Nat)))
  (orb : List (List (Nat × Nat × Nat))) (reps : List (List Nat)) (ranks : List (List (List Nat)))
  (recs : List (List (List (List Nat × List (List Nat)))))
  (cls : List (List Nat × List (List Nat) × List (List Nat)))

end
