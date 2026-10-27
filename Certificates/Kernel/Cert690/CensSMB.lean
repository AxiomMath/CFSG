module

public import Certificates.Data.Kernel.Cert690.CensusS
public meta import CFSG.Certificates.Kernel.Common.JsonGz
public meta import CFSG.Certificates.Kernel.Common.Repo
public import CFSG.Certificates.Kernel.Common.JsonGz
public import CFSG.Certificates.Kernel.Common.Repo

set_option maxRecDepth 400000

public section

#kc_repo #kc_json_gz CertificateChecks.KernelC690.CensSM
  "Certificates/Kernel/Cert690/data/CensSMB.json.gz" 39001 17476474802104581485
  (b : Nat) (nS : Nat) (spk : Nat) (nF : Nat) (sing : List Nat) (tpT : List Nat)
  (tpI : List Nat) (og : List Nat) (omg : List Nat) (kpg : List Nat) (pglc : List Nat)
  (LG : List (List Nat)) (LC : List (List Nat)) (fc : List Nat) (fg : List (List Nat))
  (cands : List Nat)

namespace CertificateChecks.KernelC690.CensSM

open CFSG.KC.C690S

@[expose] noncomputable def base : SBase :=
  ⟨false, b, nS, spk, nF, sing, tpT, tpI, og, omg, kpg, pglc, LG, LC, fc, fg⟩

end CertificateChecks.KernelC690.CensSM

end
