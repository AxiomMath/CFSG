module

public import Init
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_json_gz CertificateChecks.KernelCo2W11.S0
  "Certificates/Kernel/Co2W11/data/sep0.json.gz" 7991 14689026209113611908
  (words : List (List Bool)) (tree : List (Nat × Nat)) (masks : List Nat) (ts : List Nat)
  (F : Nat) (Dm : Nat) (w : Nat) (spinTree : List (Nat × Nat)) (spinV : Nat) (spinE : Nat)
  (spinRi : Nat)

#kc_repo #kc_json_gz CertificateChecks.KernelCo2W11.S1
  "Certificates/Kernel/Co2W11/data/sep1.json.gz" 5490 8482119864291991665
  (words : List (List Bool)) (tree : List (Nat × Nat)) (masks : List Nat) (ts : List Nat)
  (F : Nat) (Dm : Nat) (w : Nat)

#kc_repo #kc_json_gz CertificateChecks.KernelCo2W11.S2
  "Certificates/Kernel/Co2W11/data/sep2.json.gz" 5097 16343065867356161753
  (words : List (List Bool)) (tree : List (Nat × Nat)) (masks : List Nat) (ts : List Nat)
  (F : Nat) (Dm : Nat) (w : Nat)

end
