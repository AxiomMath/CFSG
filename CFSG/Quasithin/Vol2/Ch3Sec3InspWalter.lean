module

public import CFSG.Foundations.Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Defs

public section

namespace CFSG.Quasithin.H13

open CFSG.QuasithinUnique

namespace S3320

@[expose] def InspWalter3320 : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (Y S H : Subgroup Q), Y.Normal → IsSimpleGroup ↥Y →
    (∃ a b : ↥Y, a * b ≠ b * a) → Subgroup.centralizer (Y : Set Q) = ⊥ →
    CFSG.IsStronglyQuasithin ↥Y → IsSylowTwoOf S ⊤ → (∀ a ∈ S, ∀ b ∈ S, a * b = b * a) →
    S ≤ H → Nonempty (↥H ⧸ CFSG.pCore 2 ↥H ≃* Equiv.Perm (Fin 3)) →
    ∀ q ∈ Subgroup.normalizer (S : Set Q), H.map (MulAut.conj q).toMonoidHom ≠ H →
      H ⊔ H.map (MulAut.conj q).toMonoidHom = ⊤

end S3320

end CFSG.Quasithin.H13
