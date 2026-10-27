module

public import Certificates.Data.Kernel.Census.HeConj2
import CFSG.Certificates.Kernel.Common.JsonGzC
import CFSG.Certificates.Kernel.Common.Repo

open CFSG.KC.Census CFSG.KC.HeConj in
#kc_repo #kc_jsonc_gz CertificateChecks.KernelCensus.HeCj
  "Certificates/Kernel/Census/HeC/data/heconj.json.gz" 113204 4580204423842970179
  (xs : List Nat) (rs : List Nat) (cjs : List (List Nat)) (bs : List (Nat × Nat)) (us : Array Nat)
  (im : List Nat) (wt : List Nat) (cm : List Nat) (cs : Array Nat) (ci : Array Nat)
  (roots : List (Nat × Nat)) (nb : Array (Array Nat)) (nm : Array (List Nat))
  (ents : Array (List (Nat × Nat × Nat))) (wits : Array HW) (ks : List Nat) (dl : List Nat)
  (fl : List Nat) (xf : List Nat)

public section

namespace CertificateChecks.KernelCensus.HeCj

open CFSG.KC.HeConj

@[expose] noncomputable def d : HeD :=
  ⟨xs, rs, cjs, bs, us, im, wt, cm, cs, ci, roots, nb, nm, ents, wits, ks, dl, fl, xf⟩

end CertificateChecks.KernelCensus.HeCj

end
