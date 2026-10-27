
module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3Img
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Delta5
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic
public import Certificates.Certificate3172

@[expose] public section

open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.A5 CFSG.QuasithinUnique.A5.Kc3Cover CFSG.Open CFSG.QuasithinUnique.A5.Delta5

namespace CertificateChecks.Batch17030

private theorem fixed_alt_zero'_0 :  ∀ v : Fin 5 → ZMod 2, isEven v →
    (∀ σ : Equiv.Perm (Fin 5), Equiv.Perm.sign σ = 1 → pact σ v = v) → v = 0  := by
  decide +kernel

end CertificateChecks.Batch17030

namespace Certificates

end Certificates
