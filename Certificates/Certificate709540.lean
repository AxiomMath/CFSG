module

public import Certificates.Kernel.WEMK.Glue

public section

namespace Certificates

open CFSG.StandardType.ZS in
theorem certificate709540 : ∀ (k : ExcRow), k.needsModel → ∀ {p : ℕ} {U : Type} [AddCommGroup U] [Module (ZMod p) U]
    {A : Subgroup (U ≃ₗ[ZMod p] U)}, OneClass p A → ModelIso p k A → ∀ r ∈ A, CFSG.StandardType.ZS.IsRefl p r → WitL51 p A r :=
  CFSG.StandardType.ZS.WEMK.wemk_wit

end Certificates
