module

public import Certificates.Kernel.Co2I301.Bind
public import Certificates.Kernel.SporSch.Co2M.Seeds
public import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#kc_repo #kc_json_gz CertificateChecks.KernelCo2I301.MX
  "Certificates/Kernel/Co2I301/data/m2300.json.gz" 2984 16377854987661079765
  (m : List (Nat × Nat))

namespace CertificateChecks.KernelCo2I301

open CFSG.KC.Enum CFSG.KS CFSG.KS.Co2M CFSG.KS.MatRep CFSG.Sporadic.Co2I301
open CertificateChecks.KernelSporSch.Co2M (PV)

@[expose] noncomputable def M (k : ℕ) : ℕ := (MX.m.getD k (0, 0)).1

@[expose] noncomputable def MI (k : ℕ) : ℕ := (MX.m.getD k (0, 0)).2

theorem bind_ok : allN 10 (fun k => bindK (PV 0) (HX.F k) (M k) (MI k)) = true := by quickRfl

theorem rep_arr (k : ℕ) (hk : k < 10) : Rep 22 CFSG.Sporadic.Co2Cert.co2PackedVecs (i301Arr k)
    (M k) (MI k) :=
  bindK_sound CertificateChecks.KernelSporSch.Co2M.good CertificateChecks.KernelSporSch.Co2M.V_size
    (fun _ hi => CertificateChecks.KernelSporSch.Co2M.V_get hi) (arr_eq k hk) (allN_spec bind_ok k hk)

end CertificateChecks.KernelCo2I301

end
