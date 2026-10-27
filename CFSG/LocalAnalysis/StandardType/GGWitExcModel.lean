module

public import Certificates.Certificate709540

public section

namespace CFSG.StandardType.ZS

theorem wit_exc_model {p : ℕ} {U : Type} [AddCommGroup U] [Module (ZMod p) U]
    {A : Subgroup (U ≃ₗ[ZMod p] U)} (k : ExcRow) (hk : k.needsModel) (hone : OneClass p A) (hmod : ModelIso p k A) :
    ∀ r ∈ A, IsRefl p r → WitL51 p A r :=
  Certificates.certificate709540 k hk hone hmod

end CFSG.StandardType.ZS

end
