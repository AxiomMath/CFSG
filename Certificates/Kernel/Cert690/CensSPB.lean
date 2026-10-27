module

public import Certificates.Data.Kernel.Cert690.CensusS
public meta import CFSG.Certificates.Kernel.Common.JsonGz
public meta import CFSG.Certificates.Kernel.Common.Repo
public import CFSG.Certificates.Kernel.Common.JsonGz
public import CFSG.Certificates.Kernel.Common.Repo

set_option maxRecDepth 400000

public section

#kc_repo #kc_json_gz CertificateChecks.KernelC690.CensSP
  "Certificates/Kernel/Cert690/data/CensSPB.json.gz" 48886 16257003476774473013
  (b : Nat) (nS : Nat) (spk : Nat) (nF : Nat) (sing : List Nat) (tpT : List Nat)
  (tpI : List Nat) (og : List Nat) (omg : List Nat) (kpg : List Nat) (pglc : List Nat)
  (LG : List (List Nat)) (LC : List (List Nat)) (fc : List Nat) (fg : List (List Nat))
  (cands : List Nat)

namespace CertificateChecks.KernelC690.CensSP

open CFSG.KC.C690S

@[expose] noncomputable def base : SBase :=
  ⟨true, b, nS, spk, nF, sing, tpT, tpI, og, omg, kpg, pglc, LG, LC, fc, fg⟩

end CertificateChecks.KernelC690.CensSP

end
