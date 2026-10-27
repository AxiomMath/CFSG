module

public import CFSG.Quasithin.EmptyFaithful.S152Defs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace S15223P4

namespace D1

variable {G : Type} [Group G] [Finite G]

structure P4N1pre (T Mc M H : Subgroup G) (B₀ : Subgroup (MulAut (V154 T Mc M)))
    (I X : Subgroup G) : Prop where
  A_sylow : IsSylowTwoOf (sOf152 T Mc M B₀ ⊓ X) X
  not_le_Mc : ¬ X ≤ Mc
  card_M0 : Nat.card ↥(X ⊓ (Mc ⊓ I)) = 3 * Nat.card ↥(sOf152 T Mc M B₀ ⊓ X)
  card_MX : Nat.card ↥(X ⊓ M) = 3 * Nat.card ↥(sOf152 T Mc M B₀ ⊓ X)
  M0_inf_MX : X ⊓ (Mc ⊓ I) ⊓ (X ⊓ M) = sOf152 T Mc M B₀ ⊓ X
  inv_MX : ∀ y ∈ X ⊓ M, y ^ 3 ∈ pCoreOf 2 X → y ∉ pCoreOf 2 X →
    ∃ g ∈ X ⊓ M, g * y * g⁻¹ * y ∈ pCoreOf 2 X

structure P4N1 (T Mc M H : Subgroup G) (B₀ : Subgroup (MulAut (V154 T Mc M)))
    (I X : Subgroup G) : Prop extends P4N1pre T Mc M H B₀ I X where
  normal : I ≤ Subgroup.normalizer (X : Set G)

end D1

end S15223P4

end CFSG.Quasithin
